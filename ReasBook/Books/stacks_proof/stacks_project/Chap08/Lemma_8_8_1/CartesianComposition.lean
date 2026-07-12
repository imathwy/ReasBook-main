import StacksProject_2024.Chap08.Lemma_8_8_1.CartesianEmbedding

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
namespace HomOver

set_option maxHeartbeats 1200000 in
/-- Source stage 3.10, sheaf-glued factorization: composing the cartesian lift with `oldMap φ`
recovers the original natural component family. -/
theorem compositionFamily_cartesianLiftToOld_oldMap
    {X : FibredCategoryOver.{u, v, uX, vX} C} {T : C}
    (hSheaf : homPresheavesAreSheaves (J := J) X)
    (D : DescentCompletionObjectOver (J := J) X T)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : T ⟶ X.p.obj a}
    (α : DescentCompletionObjectOver.NaturalHomOver (J := J) D
      (DescentCompletionObject.oldObject (J := J) X b).object
      (g ≫ X.p.map φ))
    {W : C} (I : D.cover.Arrow)
    (L : (DescentCompletionObject.oldObject (J := J) X b).object.cover.Arrow)
    (i : W ⟶ I.Y) (l : W ⟶ L.Y)
    (h : i ≫ I.f ≫ (g ≫ X.p.map φ) = l ≫ L.f) :
    compositionFamily (J := J) hSheaf
        (cartesianLiftToOldHomOver (J := J) D φ hφ α.toHomOver)
        (DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver
        (DescentCompletionObjectOver.NaturalHomOver.cartesianLiftToOld
          (J := J) D φ hφ α).naturality
        (DescentCompletionObject.oldMap (J := J) X φ).components.naturality
        I L i l h =
      α.toHomOver.family I L i l h := by
  let β := cartesianLiftToOldHomOver (J := J) D φ hφ α.toHomOver
  let old := (DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver
  let hβnat : HomOver.familyNaturality' (J := J) β :=
    (DescentCompletionObjectOver.NaturalHomOver.cartesianLiftToOld
      (J := J) D φ hφ α).naturality
  let holdnat : HomOver.familyNaturality' (J := J) old :=
    (DescentCompletionObject.oldMap (J := J) X φ).components.naturality
  let S := compositionMiddleCover (J := J)
    (D := D)
    (E := (DescentCompletionObject.oldObject (J := J) X a).object)
    (H := (DescentCompletionObject.oldObject (J := J) X b).object)
    (f := g) (g := X.p.map φ) I L i l
      (by simpa [Category.assoc] using h)
  apply fiberHom_ext_of_cover (J := J) X.p S
    (D.restrictedLocalObject I i)
    ((DescentCompletionObject.oldObject (J := J) X b).object.restrictedLocalObject L l)
    (hSheaf W (D.restrictedLocalObject I i)
      ((DescentCompletionObject.oldObject (J := J) X b).object.restrictedLocalObject L l))
  intro Kp
  let hsmall :
      (Kp.f ≫ i) ≫ I.f ≫ (g ≫ X.p.map φ) = (Kp.f ≫ l) ≫ L.f := by
    simpa [Category.assoc] using congrArg (fun q => Kp.f ≫ q) h
  let hβK : (Kp.f ≫ i) ≫ I.f ≫ g = 𝟙 Kp.Y ≫ Kp.base.f := by
    dsimp [S, compositionMiddleCover]
    simp [Category.assoc]
    rfl
  let hOldK : 𝟙 Kp.Y ≫ Kp.base.f ≫ X.p.map φ = (Kp.f ≫ l) ≫ L.f := by
    simpa [S, compositionMiddleCover, Category.assoc] using
      congrArg (fun q => Kp.f ≫ q) h
  let localComp :=
    localComposite (J := J) β old I Kp.base L
      (Kp.f ≫ i) (𝟙 Kp.Y) (Kp.f ≫ l) hβK hOldK
  have hleftPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf β old hβnat holdnat I L i l h)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl =
        localComp := by
    have hglue := compositionGluedComponent_pullHom_of_fac (J := J)
      β old hβnat holdnat I L i l
      (by simpa [Category.assoc] using h)
      (hSheaf W (D.restrictedLocalObject I i)
        ((DescentCompletionObject.oldObject (J := J) X b).object.restrictedLocalObject L l))
      Kp (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl hβK hOldK
    simpa [compositionFamily, localComp, β, old, hβnat, holdnat, Category.assoc] using hglue
  have hlocal :
      localComp =
        α.toHomOver.family I L (Kp.f ≫ i) (Kp.f ≫ l) hsmall := by
    simpa [localComp, localComposite, β, old] using
      cartesianLiftToOldHomOver_oldMap_comp
        (J := J) D φ hφ α.toHomOver I Kp.base L
        (Kp.f ≫ i) (𝟙 Kp.Y) (Kp.f ≫ l) hβK hOldK
  have hrightPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (α.toHomOver.family I L i l h)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl =
        α.toHomOver.family I L (Kp.f ≫ i) (Kp.f ≫ l) hsmall := by
    simpa [hsmall] using
      α.naturality I L i l h Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl
  have hpull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf β old hβnat holdnat I L i l h)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (α.toHomOver.family I L i l h)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl := by
    rw [hleftPull, hrightPull, hlocal]
  have hmapLeft :=
    Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (F := canonicalFiberPseudofunctor X.p)
      (φ := compositionFamily (J := J) hSheaf β old hβnat holdnat I L i l h)
      Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl
  have hmapRight :=
    Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (F := canonicalFiberPseudofunctor X.p)
      (φ := α.toHomOver.family I L i l h)
      Kp.f (Kp.f ≫ i) (Kp.f ≫ l) rfl rfl
  rw [hmapLeft, hmapRight, hpull]

set_option maxHeartbeats 1200000 in
/-- Source stage 3.10, sheaf-glued composition with an old-object cartesian arrow is locally the
obvious componentwise composite.  This is the converse factorization input for uniqueness of the
cartesian lift. -/
theorem compositionFamily_oldMap_eq_local
    {X : FibredCategoryOver.{u, v, uX, vX} C} {T : C}
    (hSheaf : homPresheavesAreSheaves (J := J) X)
    (D : DescentCompletionObjectOver (J := J) X T)
    {a b : X.S} (φ : a ⟶ b)
    {g : T ⟶ X.p.obj a}
    (β : DescentCompletionObjectOver.NaturalHomOver (J := J) D
      (DescentCompletionObject.oldObject (J := J) X a).object g)
    {W : C} (I : D.cover.Arrow)
    (K : (DescentCompletionObject.oldObject (J := J) X a).object.cover.Arrow)
    (i : W ⟶ I.Y) (k : W ⟶ K.Y)
    (h : i ≫ I.f ≫ g = k ≫ K.f) :
    let L := oldMapTargetCoverArrow (J := J) φ K
    let hα := cartesianLiftToOld_hα (J := J) φ I K i k h
    let hOld := cartesianLiftToOld_hOld (J := J) φ K k
    compositionFamily (J := J) hSheaf β.toHomOver
        (DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver
        β.naturality
        (DescentCompletionObject.oldMap (J := J) X φ).components.naturality
        I L i k hα =
      β.toHomOver.family I K i k h ≫
        (DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver.family
          K L k k hOld := by
  intro L hα hOld
  let old := (DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver
  let holdnat : familyNaturality' (J := J) old :=
    (DescentCompletionObject.oldMap (J := J) X φ).components.naturality
  let S := compositionMiddleCover (J := J)
    (D := D)
    (E := (DescentCompletionObject.oldObject (J := J) X a).object)
    (H := (DescentCompletionObject.oldObject (J := J) X b).object)
    (f := g) (g := X.p.map φ) I L i k
      (by simpa [L, oldMapTargetCoverArrow, Category.assoc] using hα)
  apply fiberHom_ext_of_cover (J := J) X.p S
    (D.restrictedLocalObject I i)
    ((DescentCompletionObject.oldObject (J := J) X b).object.restrictedLocalObject L k)
    (hSheaf W (D.restrictedLocalObject I i)
      ((DescentCompletionObject.oldObject (J := J) X b).object.restrictedLocalObject L k))
  intro Kp
  let hsmall :
      (Kp.f ≫ i) ≫ I.f ≫ (g ≫ X.p.map φ) = (Kp.f ≫ k) ≫ L.f := by
    simpa [L, oldMapTargetCoverArrow, Category.assoc] using
      congrArg (fun q => Kp.f ≫ q) hα
  let hβKp : (Kp.f ≫ i) ≫ I.f ≫ g = 𝟙 Kp.Y ≫ Kp.base.f := by
    dsimp [S, compositionMiddleCover]
    simp [Category.assoc]
    rfl
  let hOldKp : 𝟙 Kp.Y ≫ Kp.base.f ≫ X.p.map φ = (Kp.f ≫ k) ≫ L.f := by
    simpa [S, compositionMiddleCover, L, oldMapTargetCoverArrow, Category.assoc] using
      congrArg (fun q => Kp.f ≫ q) hα
  let hβsmall : (Kp.f ≫ i) ≫ I.f ≫ g = (Kp.f ≫ k) ≫ K.f := by
    simpa [Category.assoc] using congrArg (fun q => Kp.f ≫ q) h
  let hOldSmall : (Kp.f ≫ k) ≫ K.f ≫ X.p.map φ = (Kp.f ≫ k) ≫ L.f := by
    simpa [L, oldMapTargetCoverArrow, Category.assoc] using
      congrArg (fun q => Kp.f ≫ q) hOld
  let localComp :=
    localComposite (J := J) β.toHomOver old I Kp.base L
      (Kp.f ≫ i) (𝟙 Kp.Y) (Kp.f ≫ k) hβKp hOldKp
  have hleftPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf β.toHomOver old β.naturality holdnat
            I L i k hα)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl =
        localComp := by
    have hglue := compositionGluedComponent_pullHom_of_fac (J := J)
      β.toHomOver old β.naturality holdnat I L i k
      (by simpa [L, oldMapTargetCoverArrow, Category.assoc] using hα)
      (hSheaf W (D.restrictedLocalObject I i)
        ((DescentCompletionObject.oldObject (J := J) X b).object.restrictedLocalObject L k))
      Kp (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl hβKp hOldKp
    simpa [compositionFamily, localComp, old, holdnat, Category.assoc] using hglue
  let βKp := β.toHomOver.family I Kp.base (Kp.f ≫ i) (𝟙 Kp.Y) hβKp
  let βK := β.toHomOver.family I K (Kp.f ≫ i) (Kp.f ≫ k) hβsmall
  let oldKp := old.family Kp.base L (𝟙 Kp.Y) (Kp.f ≫ k) hOldKp
  let oldK := old.family K L (Kp.f ≫ k) (Kp.f ≫ k) hOldSmall
  let e :=
    ((DescentCompletionObject.oldObject (J := J) X a).object.overlapIso
      (I₁ := Kp.base) (I₂ := K) (𝟙 Kp.Y) (Kp.f ≫ k)
        (by
          exact (Eq.trans hβKp.symm hβsmall))).hom
  have hβcompat : βK = βKp ≫ e := by
    have hcompat := β.toHomOver.compatible I I Kp.base K
      (Kp.f ≫ i) (Kp.f ≫ i) (𝟙 Kp.Y) (Kp.f ≫ k)
      rfl
      (by
        exact (Eq.trans hβKp.symm hβsmall))
      hβKp hβsmall
    rw [DescentCompletionObjectOver.overlapIso_self_hom (J := J) D I (Kp.f ≫ i)]
      at hcompat
    simpa [βKp, βK, e] using hcompat
  have hOldCompat : e ≫ oldK = oldKp := by
    have hcompat := old.compatible Kp.base K L L
      (𝟙 Kp.Y) (Kp.f ≫ k) (Kp.f ≫ k) (Kp.f ≫ k)
      (by
        exact (Eq.trans hβKp.symm hβsmall))
      rfl hOldKp hOldSmall
    rw [DescentCompletionObjectOver.overlapIso_self_hom
      (J := J) (DescentCompletionObject.oldObject (J := J) X b).object L (Kp.f ≫ k)]
      at hcompat
    simpa [oldKp, oldK, e] using hcompat
  have hlocal : localComp = βK ≫ oldK := by
    calc
      localComp = βKp ≫ oldKp := by
        rfl
      _ = βKp ≫ (e ≫ oldK) := by
        rw [← hOldCompat]
      _ = (βKp ≫ e) ≫ oldK := by
        rw [Category.assoc]
      _ = βK ≫ oldK := by
        rw [← hβcompat]
  have hrightPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (β.toHomOver.family I K i k h ≫
            old.family K L k k hOld)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl =
        βK ≫ oldK := by
    have hpullComp :
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := canonicalFiberPseudofunctor X.p)
            (β.toHomOver.family I K i k h ≫ old.family K L k k hOld)
            Kp.f (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl =
          Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              (F := canonicalFiberPseudofunctor X.p)
              (β.toHomOver.family I K i k h) Kp.f
              (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl ≫
            Pseudofunctor.LocallyDiscreteOpToCat.pullHom
              (F := canonicalFiberPseudofunctor X.p)
              (old.family K L k k hOld) Kp.f
              (Kp.f ≫ k) (Kp.f ≫ k) rfl rfl := by
        simpa using
          Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp
            (F := canonicalFiberPseudofunctor X.p)
            (β.toHomOver.family I K i k h) (old.family K L k k hOld)
            Kp.f (Kp.f ≫ i) (Kp.f ≫ k) (Kp.f ≫ k) rfl rfl rfl
    have hβNat :
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := canonicalFiberPseudofunctor X.p)
            (β.toHomOver.family I K i k h) Kp.f
            (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl =
          βK := by
      simpa [βK, hβsmall] using
        β.naturality I K i k h Kp.f (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl
    have hOldNat :
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := canonicalFiberPseudofunctor X.p)
            (old.family K L k k hOld) Kp.f
            (Kp.f ≫ k) (Kp.f ≫ k) rfl rfl =
          oldK := by
      simpa [oldK, hOldSmall] using
        holdnat K L k k hOld Kp.f (Kp.f ≫ k) (Kp.f ≫ k) rfl rfl
    rw [hpullComp, hβNat, hOldNat]
    rfl
  have hpull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf β.toHomOver old β.naturality holdnat
            I L i k hα)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (β.toHomOver.family I K i k h ≫ old.family K L k k hOld)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl := by
    rw [hleftPull, hrightPull, hlocal]
  have hmapLeft :=
    Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (F := canonicalFiberPseudofunctor X.p)
      (φ := compositionFamily (J := J) hSheaf β.toHomOver old β.naturality holdnat
        I L i k hα)
      Kp.f (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl
  have hmapRight :=
    Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (F := canonicalFiberPseudofunctor X.p)
      (φ := β.toHomOver.family I K i k h ≫
        (DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver.family K L k k hOld)
      Kp.f (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl
  rw [hmapLeft]
  have hpullActual :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (compositionFamily (J := J) hSheaf β.toHomOver old β.naturality holdnat
            I L i k hα)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := canonicalFiberPseudofunctor X.p)
          (β.toHomOver.family I K i k h ≫
            (DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver.family K L k k hOld)
          Kp.f (Kp.f ≫ i) (Kp.f ≫ k) rfl rfl := by
    simpa [old] using hpull
  rw [hpullActual]
  exact hmapRight.symm

set_option maxHeartbeats 1200000 in
/-- Source stage 3.10, component uniqueness: lifting the glued composite `β ≫ G(φ)` back along
the original cartesian arrow `φ` recovers the original component family `β`. -/
theorem cartesianLiftToOldHomOver_compose_oldMap_family
    {X : FibredCategoryOver.{u, v, uX, vX} C} {T : C}
    (hSheaf : homPresheavesAreSheaves (J := J) X)
    (D : DescentCompletionObjectOver (J := J) X T)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : T ⟶ X.p.obj a}
    (β : DescentCompletionObjectOver.NaturalHomOver (J := J) D
      (DescentCompletionObject.oldObject (J := J) X a).object g)
    {W : C} (I : D.cover.Arrow)
    (K : (DescentCompletionObject.oldObject (J := J) X a).object.cover.Arrow)
    (i : W ⟶ I.Y) (k : W ⟶ K.Y)
    (h : i ≫ I.f ≫ g = k ≫ K.f) :
    let α := DescentCompletionObjectOver.NaturalHomOver.compose (J := J) hSheaf β
      (DescentCompletionObject.oldMap (J := J) X φ).components
    (cartesianLiftToOldHomOver (J := J) D φ hφ α.toHomOver).family I K i k h =
      β.toHomOver.family I K i k h := by
  intro α
  let L := oldMapTargetCoverArrow (J := J) φ K
  let hα := cartesianLiftToOld_hα (J := J) φ I K i k h
  let hOld := cartesianLiftToOld_hOld (J := J) φ K k
  let δ := (cartesianLiftToOldHomOver (J := J) D φ hφ α.toHomOver).family I K i k h
  let βcomp := β.toHomOver.family I K i k h
  let oldComp :=
    (DescentCompletionObject.oldMap (J := J) X φ).components.toHomOver.family
      K L k k hOld
  have hδfac :
      δ ≫ oldComp = α.toHomOver.family I L i k hα := by
    simpa [δ, oldComp, L, hα, hOld] using
      cartesianLiftToOldHomOver_fac (J := J) D φ hφ α.toHomOver I K i k h
  have hβfac :
      α.toHomOver.family I L i k hα = βcomp ≫ oldComp := by
    simpa [α, DescentCompletionObjectOver.NaturalHomOver.compose,
      DescentCompletionObjectOver.NaturalHomOver.composeOfNaturality,
      DescentCompletionObjectOver.NaturalHomOver.composeCandidate,
      DescentCompletionObjectOver.HomOver.composeOfFamilyNaturality,
      βcomp, oldComp, L, hα, hOld] using
        compositionFamily_oldMap_eq_local
          (J := J) hSheaf D φ β I K i k h
  have hfac : δ ≫ oldComp = βcomp ≫ oldComp := hδfac.trans hβfac
  apply Functor.Fiber.hom_ext
  change δ.1 = βcomp.1
  let xF : X.p.Fiber (X.p.obj a) := Functor.Fiber.mk (p := X.p) (a := a) rfl
  let yF : X.p.Fiber (X.p.obj b) := Functor.Fiber.mk (p := X.p) (a := b) rfl
  let xMap := DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X xF K k
  let yMap := DescentCompletionObjectOver.ofFiberObjectRestrictedMap (J := J) X yF L k
  have hxMapCart : X.p.IsStronglyCartesian (k ≫ K.f) xMap :=
    DescentCompletionObjectOver.ofFiberObjectRestrictedMap_isStronglyCartesian
      (J := J) X xF K k
  have hxMapLift : X.p.IsHomLift (k ≫ K.f) xMap := hxMapCart.toIsHomLift
  have hδLift : X.p.IsHomLift (𝟙 W) δ.1 := δ.2
  have hβLift : X.p.IsHomLift (𝟙 W) βcomp.1 := βcomp.2
  have hδXLift : X.p.IsHomLift (k ≫ K.f) (δ.1 ≫ xMap) := by
    have hcomp : X.p.IsHomLift (𝟙 W ≫ (k ≫ K.f)) (δ.1 ≫ xMap) :=
      @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ (𝟙 W) (k ≫ K.f)
        δ.1 xMap hδLift hxMapLift
    simpa using hcomp
  have hβXLift : X.p.IsHomLift (k ≫ K.f) (βcomp.1 ≫ xMap) := by
    have hcomp : X.p.IsHomLift (𝟙 W ≫ (k ≫ K.f)) (βcomp.1 ≫ xMap) :=
      @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ (𝟙 W) (k ≫ K.f)
        βcomp.1 xMap hβLift hxMapLift
    simpa using hcomp
  have hφLift : X.p.IsHomLift (X.p.map φ) φ := hφ.toIsHomLift
  have hOldFac : oldComp.1 ≫ yMap = xMap ≫ φ := by
    simpa [DescentCompletionObject.oldMap, DescentCompletionObject.oldObject,
      xF, yF, xMap, yMap, oldComp, L] using
      @DescentCompletionObjectOver.ofFiberHomComponent_fac _ _ J X
        (X.p.obj a) (X.p.obj b) W
        xF yF (X.p.map φ) φ hφLift K L k k hOld
  have hproj : (δ.1 ≫ xMap) ≫ φ = (βcomp.1 ≫ xMap) ≫ φ := by
    have hfacVal : (δ ≫ oldComp).1 = (βcomp ≫ oldComp).1 :=
      congrArg Subtype.val hfac
    have hδproj :
        (δ.1 ≫ xMap) ≫ φ = (δ.1 ≫ oldComp.1) ≫ yMap := by
      simpa [Category.assoc] using congrArg (fun q => δ.1 ≫ q) hOldFac.symm
    have hβproj :
        (βcomp.1 ≫ xMap) ≫ φ = (βcomp.1 ≫ oldComp.1) ≫ yMap := by
      simpa [Category.assoc] using congrArg (fun q => βcomp.1 ≫ q) hOldFac.symm
    have hmiddle :
        (δ.1 ≫ oldComp.1) ≫ yMap = (βcomp.1 ≫ oldComp.1) ≫ yMap := by
      change (δ ≫ oldComp).1 ≫ yMap = (βcomp ≫ oldComp).1 ≫ yMap
      exact congrArg (fun q => q ≫ yMap) hfacVal
    exact hδproj.trans (hmiddle.trans hβproj.symm)
  have hx :
      δ.1 ≫ xMap = βcomp.1 ≫ xMap := by
    letI : X.p.IsStronglyCartesian (X.p.map φ) φ := hφ
    letI : X.p.IsHomLift (k ≫ K.f) (δ.1 ≫ xMap) := hδXLift
    letI : X.p.IsHomLift (k ≫ K.f) (βcomp.1 ≫ xMap) := hβXLift
    exact @Functor.IsStronglyCartesian.ext _ _ _ _ X.p
      (X.p.obj a) (X.p.obj b) a b
      (X.p.map φ) φ hφ
      W (D.restrictedLocalObject I i).1
      (k ≫ K.f) (δ.1 ≫ xMap) (βcomp.1 ≫ xMap) hδXLift hβXLift hproj
  letI : X.p.IsStronglyCartesian (k ≫ K.f) xMap := hxMapCart
  letI : X.p.IsHomLift (𝟙 W) δ.1 := hδLift
  letI : X.p.IsHomLift (𝟙 W) βcomp.1 := hβLift
  exact @Functor.IsStronglyCartesian.ext _ _ _ _ X.p
    W (X.p.obj a)
    ((DescentCompletionObject.oldObject (J := J) X a).object.restrictedLocalObject K k).1 a
    (k ≫ K.f) xMap hxMapCart
    W (D.restrictedLocalObject I i).1
    (𝟙 W) δ.1 βcomp.1 hδLift hβLift hx

end HomOver

namespace NaturalHomOver

/-- Source stage 3.10, bundled left inverse: pulling back `β ≫ G(φ)` along the original
cartesian arrow `φ` recovers `β`. -/
theorem cartesianLiftToOld_compose_oldMap
    {X : FibredCategoryOver.{u, v, uX, vX} C} {T : C}
    (hSheaf : HomOver.homPresheavesAreSheaves (J := J) X)
    (D : DescentCompletionObjectOver (J := J) X T)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : T ⟶ X.p.obj a}
    (β : DescentCompletionObjectOver.NaturalHomOver (J := J) D
      (DescentCompletionObject.oldObject (J := J) X a).object g) :
    cartesianLiftToOld (J := J) D φ hφ
        (compose (J := J) hSheaf β
          (DescentCompletionObject.oldMap (J := J) X φ).components) =
      β := by
  apply ext_family
  intro W I K i k h
  simpa [cartesianLiftToOld] using
    HomOver.cartesianLiftToOldHomOver_compose_oldMap_family
      (J := J) hSheaf D φ hφ β I K i k h

end NaturalHomOver
end DescentCompletionObjectOver

namespace DescentCompletionObject
namespace Hom

set_option maxHeartbeats 1200000 in
/-- Source stage 3.10, total factorization for the strict cartesian lift: after sheaf-glued
composition with the old-object arrow `G(φ)`, the lifted morphism recovers the original morphism
over the strict composite base `g ≫ p(φ)`. -/
theorem cartesianLiftToOldOfComponents_comp_oldMap
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (D : DescentCompletionObject (J := J) X)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : D.base ⟶ X.p.obj a}
    (α : DescentCompletionObjectOver.NaturalHomOver (J := J) D.object
      (oldObject (J := J) X b).object (g ≫ X.p.map φ)) :
    Hom.compose (J := J) hSheaf
        (cartesianLiftToOldOfComponents (J := J) D φ hφ α)
        (oldMap (J := J) X φ) =
      ({ base := g ≫ X.p.map φ
         components := α } : Hom (J := J) D (oldObject (J := J) X b)) := by
  refine Hom.ext_base_family
    (Hom.compose (J := J) hSheaf
      (cartesianLiftToOldOfComponents (J := J) D φ hφ α)
      (oldMap (J := J) X φ))
    ({ base := g ≫ X.p.map φ
       components := α } : Hom (J := J) D (oldObject (J := J) X b)) ?_ ?_
  · simp [Hom.compose, cartesianLiftToOldOfComponents, oldMap]
    rfl
  · intro W I L i l h
    simpa [Hom.compose, DescentCompletionObjectOver.NaturalHomOver.compose,
      DescentCompletionObjectOver.NaturalHomOver.composeOfNaturality,
      DescentCompletionObjectOver.NaturalHomOver.composeCandidate,
      DescentCompletionObjectOver.HomOver.composeOfFamilyNaturality,
      cartesianLiftToOldOfComponents, oldMap] using
        DescentCompletionObjectOver.HomOver.compositionFamily_cartesianLiftToOld_oldMap
          (J := J) hSheaf D.object φ hφ α I L i l h

/-- Source stage 3.10, total factorization with a propositional base equality.  This is the form
used by the universal property of a strongly cartesian arrow. -/
theorem cartesianLiftToOld_comp_oldMap
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (D : DescentCompletionObject (J := J) X)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    {g : D.base ⟶ X.p.obj a}
    (α : Hom (J := J) D (oldObject (J := J) X b))
    (hαbase : g ≫ X.p.map φ = α.base) :
    Hom.compose (J := J) hSheaf
        (cartesianLiftToOld (J := J) D φ hφ α hαbase)
        (oldMap (J := J) X φ) = α := by
  cases α with
  | mk abase acomp =>
    dsimp at hαbase
    subst abase
    simpa [cartesianLiftToOld] using
      cartesianLiftToOldOfComponents_comp_oldMap
        (J := J) hSheaf D φ hφ acomp

/-- Source stage 3.10, total left inverse: pulling back a composite `β ≫ G(φ)` along `G(φ)`
recovers `β`. -/
theorem cartesianLiftToOld_compose_oldMap_self
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (D : DescentCompletionObject (J := J) X)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ)
    (β : Hom (J := J) D (oldObject (J := J) X a)) :
    cartesianLiftToOld (J := J) D φ hφ (g := β.base)
        (Hom.compose (J := J) hSheaf β (oldMap (J := J) X φ))
        (by
          simp [Hom.compose, oldMap]
          rfl) =
      β := by
  cases β with
  | mk g βcomp =>
    simpa [cartesianLiftToOld, cartesianLiftToOldOfComponents, Hom.compose] using
      DescentCompletionObjectOver.NaturalHomOver.cartesianLiftToOld_compose_oldMap
        (J := J) hSheaf D.object φ hφ βcomp

end Hom

set_option maxHeartbeats 800000 in
/-- Source stage 3.10, the old-object embedding sends strongly cartesian arrows of the original
fibred category to strongly cartesian arrows in the descent-completion category. -/
theorem oldMap_isStronglyCartesian
    (X : FibredCategoryOver.{u, v, uX, vX} C)
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {a b : X.S} (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ) :
    letI := category (J := J) hSheaf
    (projectionFunctor (J := J) hSheaf).IsStronglyCartesian
      (X.p.map φ) (oldMap (J := J) X φ) := by
  letI := category (J := J) hSheaf
  let p' := projectionFunctor (J := J) hSheaf
  letI : p'.IsHomLift (X.p.map φ) (oldMap (J := J) X φ) :=
    by
      change p'.IsHomLift (p'.map (oldMap (J := J) X φ)) (oldMap (J := J) X φ)
      exact Functor.IsHomLift.map (p := p') (oldMap (J := J) X φ)
  refine Functor.IsStronglyCartesian.mk ?_
  intro D g α hαlift
  have hαbase : g ≫ X.p.map φ = α.base := by
    letI : p'.IsHomLift (g ≫ X.p.map φ) α := hαlift
    have hfac := IsHomLift.fac' p' (g ≫ X.p.map φ) α
    simpa [p', projectionFunctor, oldObject, oldMap, Category.assoc] using hfac.symm
  let χ := Hom.cartesianLiftToOld (J := J) D φ hφ (g := g) α hαbase
  refine ⟨χ, ?_, ?_⟩
  · constructor
    · change p'.IsHomLift (p'.map χ) χ
      exact Functor.IsHomLift.map (p := p') χ
    · simpa [χ, p'] using
        Hom.cartesianLiftToOld_comp_oldMap
          (J := J) hSheaf D φ hφ α hαbase
  · intro y hy
    rcases hy with ⟨hylift, hyfac⟩
    letI : p'.IsHomLift g y := hylift
    have hybase : g = y.base := by
      have hfac := IsHomLift.fac' p' g y
      simpa [p', projectionFunctor, oldObject, Category.assoc] using hfac.symm
    cases hybase
    have hyfac' : Hom.compose (J := J) hSheaf y (oldMap (J := J) X φ) = α := by
      simpa [p'] using hyfac
    cases hyfac'
    have hleft :=
      Hom.cartesianLiftToOld_compose_oldMap_self
        (J := J) hSheaf D φ hφ y
    simpa [χ, p'] using hleft.symm

/-- Source stage 3.10, bundled preservation statement for the old-object based functor. -/
theorem oldObjectBasedFunctor_preservesStronglyCartesian
    (X : FibredCategoryOver.{u, v, uX, vX} C)
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X) :
    (oldObjectBasedFunctor (J := J) X hSheaf).PreservesStronglyCartesian := by
  intro a b φ hφ
  simpa [oldObjectBasedFunctor, oldObjectFunctor] using
    oldMap_isStronglyCartesian (J := J) X hSheaf φ hφ

end DescentCompletionObject
end FibredCategoryMor
end CategoryTheory
