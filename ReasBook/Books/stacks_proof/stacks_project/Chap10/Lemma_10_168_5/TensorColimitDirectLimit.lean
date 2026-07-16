import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_127_5
import stacks_proof.stacks_project.Chap10.Lemma_10_131_9
import stacks_proof.stacks_project.Chap10.Lemma_10_131_14
import stacks_proof.stacks_project.Chap10.Lemma_10_151_2
import stacks_proof.stacks_project.Chap10.Lemma_10_168_5.DirectedRingLimit

-- Stable helper declarations split out for Lemma 10.168.5.

open CategoryTheory Limits
open scoped TensorProduct

universe u v

section

variable {A₀ : Type u} [CommRing A₀]
variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ CommAlgCat.{u} A₀) [HasColimit F]
variable {B₀ C₀ : Type u} [CommRing B₀] [CommRing C₀]
variable [Algebra A₀ B₀] [Algebra A₀ C₀]


/-- Helper for Lemma 10.168.5: after pushing out a directed system of `A₀`-algebras along
`A₀ → R₀`, the resulting diagram in `CommAlgCat R₀` is the canonical tensor-base-change
diagram. -/
noncomputable abbrev tensor_base_change_commAlgDiagram
    {I : Type v} [Preorder I]
    (G : I ⥤ CommAlgCat.{u} A₀)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀] :
    I ⥤ CommAlgCat.{u} R₀ :=
  G ⋙ (commAlgCatEquivUnder (CommRingCat.of A₀)).functor ⋙
    Under.pushout (CommRingCat.ofHom (algebraMap A₀ R₀)) ⋙
    (commAlgCatEquivUnder (CommRingCat.of R₀)).inverse

/-- Helper for Lemma 10.168.5: the tensor-base-changed colimit cocone in `CommAlgCat R₀`. -/
noncomputable abbrev tensor_base_change_commAlgCocone
    {I : Type v} [Preorder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀] :
    Cocone (tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀) :=
  ((commAlgCatEquivUnder (CommRingCat.of R₀)).inverse.mapCocone
    ((Under.pushout (CommRingCat.ofHom (algebraMap A₀ R₀))).mapCocone
      ((commAlgCatEquivUnder (CommRingCat.of A₀)).functor.mapCocone c.cocone)))

/-- Helper for Lemma 10.168.5: the tensor-base-changed cocone is colimiting already in
`CommAlgCat R₀`. -/
noncomputable def tensor_base_change_commAlgCocone_isColimit
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀] :
    IsColimit (tensor_base_change_commAlgCocone (A₀ := A₀) G c R₀) := by
  let E₀ := commAlgCatEquivUnder (CommRingCat.of A₀)
  let P := Under.pushout (CommRingCat.ofHom (algebraMap A₀ R₀))
  let E₁ := commAlgCatEquivUnder (CommRingCat.of R₀)
  have hUnder : IsColimit (E₀.functor.mapCocone c.cocone) := by
    -- Proof comment: first move the original colimit cocone to the under-category over `A₀`.
    exact isColimitOfPreserves E₀.functor c.isColimit
  have hPush : IsColimit (P.mapCocone (E₀.functor.mapCocone c.cocone)) := by
    -- Proof comment: pushout along `A₀ → R₀` preserves colimits because it is a left adjoint.
    exact isColimitOfPreserves P hUnder
  -- Proof comment: transport the pushed-out colimit cocone back across the equivalence with
  -- `CommAlgCat R₀`.
  simpa [tensor_base_change_commAlgCocone, tensor_base_change_commAlgDiagram, E₀, E₁, P,
    commAlgCatEquivUnder] using
    (isColimitOfPreserves E₁.inverse hPush)

/-- Helper for Lemma 10.168.5: after forgetting the tensor-base-change cocone to types, applying
the usual `Type`-level `uliftFunctor` preserves any already-available small-universe colimit
witness in the larger universe. -/
noncomputable def tensor_base_change_underlying_cocone_small_ulift_isColimit
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀]
    (hsmall :
      IsColimit ((forget CommRingCat).mapCocone
        (tensor_base_change_underlying_cocone (A₀ := A₀) G c R₀))) :
    IsColimit
      (((forget CommRingCat) ⋙ CategoryTheory.uliftFunctor.{max u v, u}).mapCocone
        (tensor_base_change_underlying_cocone (A₀ := A₀) G c R₀)) := by
  -- Proof comment: once the underlying commutative-ring cocone is colimiting in the small
  -- universe, the ordinary `Type`-level `uliftFunctor` transports that witness to the larger
  -- universe where the explicit direct-limit representatives live.
  exact isColimitOfPreserves CategoryTheory.uliftFunctor.{max u v, u} hsmall

/-- Helper for Lemma 10.168.5: the lifted direct-limit stage maps are natural for the
tensor-base-changed underlying diagram. -/
theorem tensor_base_change_ringDirectLimit_uliftTypeCocone_naturality
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀]
    {i j : I} (f : i ⟶ j) :
    (fun x : ULift.{max u v, u}
        ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i) ↦
      ULift.up
        (Ring.DirectLimit.of
          (fun i ↦ ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i))
          (fun _ _ h ↦
            ((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom)
          j (((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map f).hom x.down))) =
    (fun x : ULift.{max u v, u}
        ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i) ↦
      ULift.up
        (Ring.DirectLimit.of
          (fun i ↦ ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i))
          (fun _ _ h ↦
            ((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom)
          i x.down)) := by
  -- Proof comment: naturality is precisely the direct-limit relation for the transition map
  -- represented by the order morphism `f`.
  ext x
  cases x using ULift.casesOn
  rename_i x
  simpa only [homOfLE_leOfHom] using
    (Ring.DirectLimit.of_f
      (G := fun i ↦ ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i))
      (f := fun _ _ h ↦
        ((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom)
      (hij := leOfHom f) (x := x))

/-- Helper for Lemma 10.168.5: the large-universe `Type` cocone with vertex the explicit
tensor-stage direct limit. -/
noncomputable def tensor_base_change_ringDirectLimit_uliftTypeCocone
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀] :
    Cocone
      (G ⋙ (commAlgCatEquivUnder (CommRingCat.of A₀)).functor ⋙
        Under.pushout (CommRingCat.ofHom (algebraMap A₀ R₀)) ⋙
        CategoryTheory.Under.forget (CommRingCat.of R₀) ⋙
        forget CommRingCat ⋙ CategoryTheory.uliftFunctor.{max u v, u}) where
  pt :=
    ULift.{max u v, max u v}
      (directed_commAlg_ringDirectLimit
        (A₀ := R₀) (tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀))
  ι :=
    { app := fun i ↦
        fun x ↦
          ULift.up
            (Ring.DirectLimit.of
              (fun i ↦ ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i))
              (fun _ _ h ↦
                ((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom)
              i x.down)
      naturality := fun _ _ f ↦
        tensor_base_change_ringDirectLimit_uliftTypeCocone_naturality
          (A₀ := A₀) G R₀ f }

/-- Helper for Lemma 10.168.5: assuming the forgotten tensor-base-change cocone is a colimit in
small `Type`, its large-universe desc map lands in the explicit tensor-stage direct limit. -/
noncomputable def tensor_base_change_ringDirectLimit_uliftDescOfForgetIsColimit
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀]
    (hsmall :
      IsColimit ((forget CommRingCat).mapCocone
        (tensor_base_change_underlying_cocone (A₀ := A₀) G c R₀))) :
    ULift.{max u v, u} ↑((tensor_base_change_commAlgCocone (A₀ := A₀) G c R₀).pt) →
      ULift.{max u v, max u v}
        (directed_commAlg_ringDirectLimit
          (A₀ := R₀) (tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀)) :=
  fun y ↦
    (tensor_base_change_underlying_cocone_small_ulift_isColimit (A₀ := A₀) G c R₀ hsmall).desc
      (tensor_base_change_ringDirectLimit_uliftTypeCocone (A₀ := A₀) G R₀) y

/-- Helper for Lemma 10.168.5: the conditional large-universe desc map evaluates on stage
representatives as the explicit `Ring.DirectLimit.of` class. -/
theorem tensor_base_change_ringDirectLimit_uliftDescOfForgetIsColimit_comp_of
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀]
    (hsmall :
      IsColimit ((forget CommRingCat).mapCocone
        (tensor_base_change_underlying_cocone (A₀ := A₀) G c R₀)))
    (i : I) (z : ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i)) :
    tensor_base_change_ringDirectLimit_uliftDescOfForgetIsColimit (A₀ := A₀) G c R₀ hsmall
        (ULift.up ((tensor_base_change_commAlgCocone (A₀ := A₀) G c R₀).ι.app i z)) =
      ULift.up
        (Ring.DirectLimit.of
          (fun i ↦ ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i))
          (fun _ _ h ↦
            ((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom)
          i z) := by
  -- Proof comment: the `fac` equation of the large lifted colimit desc is exactly the required
  -- stage-computation formula.
  have hfac :=
    (tensor_base_change_underlying_cocone_small_ulift_isColimit (A₀ := A₀) G c R₀ hsmall).fac
      (tensor_base_change_ringDirectLimit_uliftTypeCocone (A₀ := A₀) G R₀) i
  simpa [tensor_base_change_ringDirectLimit_uliftDescOfForgetIsColimit,
    tensor_base_change_ringDirectLimit_uliftTypeCocone] using congrFun hfac (ULift.up z)

/-- Helper for Lemma 10.168.5: the canonical algebra map from the explicit tensor-stage direct
limit to the tensor-base-changed cocone point. -/
noncomputable abbrev tensor_base_change_ringDirectLimitToCoconePointAlgHom
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀] :
    directed_commAlg_ringDirectLimit
        (A₀ := R₀) (tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀) →ₐ[R₀]
      ↑((tensor_base_change_commAlgCocone (A₀ := A₀) G c R₀).pt) :=
  directed_commAlg_ringDirectLimitDescAlgHom
    (A₀ := R₀) (tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀)
    (tensor_base_change_commAlgCocone (A₀ := A₀) G c R₀)

/-- Helper for Lemma 10.168.5: the canonical tensor-base-change desc map evaluates on a stage
class by the corresponding tensor-base-change cocone leg. -/
@[simp]
theorem tensor_base_change_ringDirectLimitToCoconePointAlgHom_comp_of
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀]
    (i : I) (z : ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i)) :
    tensor_base_change_ringDirectLimitToCoconePointAlgHom (A₀ := A₀) G c R₀
        (Ring.DirectLimit.of
          (fun i ↦ ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i))
          (fun i j h ↦
            ((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom)
          i z) =
      (tensor_base_change_commAlgCocone (A₀ := A₀) G c R₀).ι.app i z := by
  -- Proof comment: this is just the general direct-limit desc evaluation formula specialized to
  -- the tensor-base-change diagram and cocone.
  exact directed_commAlg_ringDirectLimitDescAlgHom_comp_of
    (A₀ := R₀) (tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀)
    (tensor_base_change_commAlgCocone (A₀ := A₀) G c R₀) i z

/-- Helper for Lemma 10.168.5: the canonical stage maps into the explicit tensor-stage ring direct
limit are compatible with the transition maps of the tensor-base-change diagram. -/
theorem tensor_base_change_ringDirectLimit_of_homOfLE
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀]
    {i j : I} (h : i ≤ j) :
    (Ring.DirectLimit.of
        (fun i ↦ ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i))
        (fun i j h ↦
          ((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom)
        j).comp (((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom) =
      Ring.DirectLimit.of
        (fun i ↦ ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i))
        (fun i j h ↦
          ((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom)
        i := by
  ext x
  change
    Ring.DirectLimit.of
        (fun i ↦ ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i))
        (fun i j h ↦
          ((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom)
        j (((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom x) =
      Ring.DirectLimit.of
        (fun i ↦ ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i))
        (fun i j h ↦
          ((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom)
        i x
  simpa using
    (Ring.DirectLimit.of_f
      (G := fun i ↦ ↑((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).obj i))
      (f := fun i j h ↦
        ((tensor_base_change_commAlgDiagram (A₀ := A₀) G R₀).map (homOfLE h)).hom)
      (hij := h) (x := x))

end
