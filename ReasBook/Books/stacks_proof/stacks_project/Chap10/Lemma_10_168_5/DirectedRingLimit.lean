import Mathlib
import StacksProject_2024.Chap10.Lemma_10_127_5
import StacksProject_2024.Chap10.Lemma_10_131_9
import StacksProject_2024.Chap10.Lemma_10_131_14
import StacksProject_2024.Chap10.Lemma_10_151_2

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


/-- Helper for Lemma 10.168.5: forgetting a filtered colimit cocone of `A₀`-algebras to
`CommRingCat` preserves its colimit property. -/
noncomputable def commAlg_forget_commRing_mapCocone_isColimit
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G) :
    IsColimit ((forget₂ (CommAlgCat.{u} A₀) CommRingCat).mapCocone c.cocone) := by
  let E := commAlgCatEquivUnder (CommRingCat.of A₀)
  have hUnder : IsColimit (E.functor.mapCocone c.cocone) := by
    -- Proof comment: transport the colimit cocone across the standard equivalence
    -- `CommAlgCat A₀ ≌ Under (CommRingCat.of A₀)`.
    exact isColimitOfPreserves E.functor c.isColimit
  -- Proof comment: the forgetful functor from the under-category preserves filtered colimits, so
  -- the underlying commutative-ring cocone is still colimiting.
  simpa [E, commAlgCatEquivUnder] using
    (isColimitOfPreserves (CategoryTheory.Under.forget (CommRingCat.of A₀)) hUnder)

/-- Helper for Lemma 10.168.5: the base-changed stage rings are obtained by pushing out the
diagram of `A₀`-algebras along `A₀ → R₀` and then forgetting to `CommRingCat`. -/
noncomputable abbrev tensor_base_change_underlying_cocone
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀] :
    Cocone
      (G ⋙ (commAlgCatEquivUnder (CommRingCat.of A₀)).functor ⋙
        Under.pushout (CommRingCat.ofHom (algebraMap A₀ R₀)) ⋙
        CategoryTheory.Under.forget (CommRingCat.of R₀)) :=
  ((CategoryTheory.Under.forget (CommRingCat.of R₀)).mapCocone
    ((Under.pushout (CommRingCat.ofHom (algebraMap A₀ R₀))).mapCocone
      ((commAlgCatEquivUnder (CommRingCat.of A₀)).functor.mapCocone c.cocone)))

/-- Helper for Lemma 10.168.5: after base change along `A₀ → R₀`, the resulting cocone of stage
rings remains colimiting after forgetting to `CommRingCat`. -/
noncomputable def tensor_base_change_underlying_cocone_isColimit
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    (R₀ : Type u) [CommRing R₀] [Algebra A₀ R₀] :
    IsColimit (tensor_base_change_underlying_cocone (A₀ := A₀) G c R₀) := by
  let E := commAlgCatEquivUnder (CommRingCat.of A₀)
  let P := Under.pushout (CommRingCat.ofHom (algebraMap A₀ R₀))
  have hUnder : IsColimit (E.functor.mapCocone c.cocone) := by
    -- Proof comment: first move the colimit cocone for `G` into the under-category over `A₀`.
    exact isColimitOfPreserves E.functor c.isColimit
  have hPush : IsColimit (P.mapCocone (E.functor.mapCocone c.cocone)) := by
    -- Proof comment: pushout in the under-category is a left adjoint, hence preserves colimits.
    exact isColimitOfPreserves P hUnder
  -- Proof comment: the forgetful functor from `Under (CommRingCat.of R₀)` preserves filtered
  -- colimits, so the base-changed cocone of underlying rings is colimiting.
  simpa [tensor_base_change_underlying_cocone, P, E, commAlgCatEquivUnder] using
    (isColimitOfPreserves (CategoryTheory.Under.forget (CommRingCat.of R₀)) hPush)

/-- Helper for Lemma 10.168.5: the underlying stage rings of a directed diagram of `A₀`-algebras
form a directed system under the transition ring maps. -/
theorem directed_commAlg_underlying_directedSystem
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G) :
    DirectedSystem
      (fun i ↦ ↑(G.obj i))
      (fun i j h ↦ (G.map (homOfLE h)).hom) := by
  let A : I → Type u := fun i ↦ ↑(G.obj i)
  let ρ : ∀ i j, i ≤ j → A i →+* A j := fun i j h ↦ (G.map (homOfLE h)).hom
  refine
    { map_self := ?_
      map_map := ?_ }
  · intro i x
    -- Proof comment: the transition map along the identity morphism is the identity by
    -- functoriality of `G`.
    change ((G.map (𝟙 i)).hom) x = x
    simpa using congrArg (fun f : G.obj i ⟶ G.obj i ↦ f x) (G.map_id i)
  · intro k j i hij hjk x
    -- Proof comment: composing two transition maps agrees with the transition along the composite
    -- order relation because `G` is a functor on the preorder category.
    change ((G.map (homOfLE hjk)).hom) (((G.map (homOfLE hij)).hom) x) =
      ((G.map (homOfLE (hij.trans hjk))).hom) x
    simpa using
      congrArg (fun f : G.obj i ⟶ G.obj k ↦ f x)
        (G.map_comp (homOfLE hij) (homOfLE hjk)).symm

/-- Helper for Lemma 10.168.5: the `CommRingCat` universe-lift functor preserves identities on
the nose after applying `RingHom.ulift`. -/
lemma entry_commRingCat_uliftFunctor_map_id (R : CommRingCat.{u}) :
    CommRingCat.ofHom
        (RingHom.ulift (RingHom.id R) : ULift.{v} R →+* ULift.{v} R) =
      𝟙 (CommRingCat.of (ULift.{v} R)) := by
  -- Proof comment: on elements, the lifted identity is literally the identity function.
  ext x
  simp [RingHom.ulift_apply]

/-- Helper for Lemma 10.168.5: the `CommRingCat` universe-lift functor sends compositions to
compositions after applying `RingHom.ulift`. -/
lemma entry_commRingCat_uliftFunctor_map_comp
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    CommRingCat.ofHom
        (RingHom.ulift (g.hom.comp f.hom) : ULift.{v} R →+* ULift.{v} T) =
      CommRingCat.ofHom
          (RingHom.ulift f.hom : ULift.{v} R →+* ULift.{v} S) ≫
        CommRingCat.ofHom
          (RingHom.ulift g.hom : ULift.{v} S →+* ULift.{v} T) := by
  -- Proof comment: both composites act by `x ↦ ULift.up (g (f x.down))`.
  ext x
  simp [RingHom.ulift_apply]

/-- Helper for Lemma 10.168.5: the literal universe-lift functor on `CommRingCat` needed for the
explicit direct-limit cocone. -/
abbrev entry_commRingCat_uliftFunctor : CommRingCat.{u} ⥤ CommRingCat.{max u v} where
  obj R := CommRingCat.of (ULift.{v} R)
  map f := CommRingCat.ofHom (RingHom.ulift f.hom)
  map_id := entry_commRingCat_uliftFunctor_map_id
  map_comp := entry_commRingCat_uliftFunctor_map_comp

/-- Helper for Lemma 10.168.5: the universe-safe ring diagram for a directed system of
`A₀`-algebras is obtained by forgetting to `CommRingCat` and then applying the chapter's
`CommRingCat` universe-lift functor. -/
abbrev directed_commAlg_toULiftCommRing
    {I : Type v} [Preorder I]
    (G : I ⥤ CommAlgCat.{u} A₀) :
    I ⥤ CommRingCat.{max u v} :=
  G ⋙ forget₂ (CommAlgCat.{u} A₀) CommRingCat ⋙ entry_commRingCat_uliftFunctor

/-- Helper for Lemma 10.168.5: on an order morphism, the lifted ring diagram uses the universe
lift of the underlying transition ring hom. -/
@[simp]
theorem directed_commAlg_toULiftCommRing_map_homOfLE
    {I : Type v} [Preorder I]
    (G : I ⥤ CommAlgCat.{u} A₀) {i j : I} (h : i ≤ j) :
    (directed_commAlg_toULiftCommRing (A₀ := A₀) G).map (homOfLE h) =
      CommRingCat.ofHom
        ((RingHom.ulift (G.map (homOfLE h)).hom) :
          ULift.{v} ↑(G.obj i) →+* ULift.{v} ↑(G.obj j)) := by
  rfl

/-- Helper for Lemma 10.168.5: the explicit ring direct limit of a directed system of
`A₀`-algebras carries the tautological cocone in `CommRingCat`. -/
noncomputable def directed_commRing_directLimitCocone
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) :
    Cocone (directed_commAlg_toULiftCommRing (A₀ := A₀) G) where
  pt := CommRingCat.of <|
    ULift.{v} <|
      Ring.DirectLimit
      (fun i ↦ ↑(G.obj i))
      (fun i j h ↦ (G.map (homOfLE h)).hom)
  ι :=
    { app := fun i ↦
        CommRingCat.ofHom <|
          ((RingHom.ulift <|
            Ring.DirectLimit.of
              (fun i ↦ ↑(G.obj i))
              (fun i j h ↦ (G.map (homOfLE h)).hom) i) :
            ULift.{v} ↑(G.obj i) →+*
              ULift.{v}
                (Ring.DirectLimit
                  (fun i ↦ ↑(G.obj i))
                  (fun i j h ↦ (G.map (homOfLE h)).hom)))
      naturality := by
        intro i j f
        -- Proof comment: the direct-limit structure maps satisfy the directed-system relation
        -- `of_j ∘ f_ij = of_i`, and `RingHom.ulift` preserves that identity on the nose.
        apply CommRingCat.hom_ext
        ext x
        cases x using ULift.casesOn
        rename_i x
        change
          ULift.up
              ((Ring.DirectLimit.of
                  (fun i ↦ ↑(G.obj i))
                  (fun i j h ↦ (G.map (homOfLE h)).hom) j)
                (((G.map f).hom) x)) =
            ULift.up
              ((Ring.DirectLimit.of
                  (fun i ↦ ↑(G.obj i))
                  (fun i j h ↦ (G.map (homOfLE h)).hom) i) x)
        exact congrArg ULift.up <|
          by
            simpa only [homOfLE_leOfHom] using
              (Ring.DirectLimit.of_f
                (G := fun i ↦ ↑(G.obj i))
                (f := fun i j h ↦ (G.map (homOfLE h)).hom)
                (leOfHom f) x) }

/-- Helper for Lemma 10.168.5: the explicit `ULift`ed `Ring.DirectLimit` cocone is already a
colimit cocone in `CommRingCat`. -/
noncomputable def directed_commRing_directLimitCocone_isColimit
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) :
    IsColimit (directed_commRing_directLimitCocone (A₀ := A₀) G) := by
  classical
  let descAux :
      ∀ s : Cocone (directed_commAlg_toULiftCommRing (A₀ := A₀) G),
        Ring.DirectLimit
            (fun i ↦ ↑(G.obj i))
            (fun i j h ↦ (G.map (homOfLE h)).hom) →+* ↑s.pt :=
    fun s ↦
      Ring.DirectLimit.lift
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        ↑s.pt
        (fun i ↦ (s.ι.app i).hom.comp
          (ULift.ringEquiv.symm : ↑(G.obj i) ≃+* ULift.{v} ↑(G.obj i)).toRingHom)
        (fun i j h x ↦ by
          -- Proof comment: cocone naturality on the lifted stage `ULift.up x` is exactly the
          -- compatibility relation needed by `Ring.DirectLimit.lift`.
          have hs :
              (((directed_commAlg_toULiftCommRing (A₀ := A₀) G).map (homOfLE h)) ≫
                  s.ι.app j).hom (ULift.up x) =
                (s.ι.app i).hom (ULift.up x) := by
            simpa using congrArg
              (fun f : (directed_commAlg_toULiftCommRing (A₀ := A₀) G).obj i ⟶ s.pt ↦
                f.hom (ULift.up x))
              (s.w (homOfLE h))
          simpa [directed_commAlg_toULiftCommRing_map_homOfLE, RingHom.comp_apply,
            RingHom.ulift_apply] using hs)
  refine
    { desc := fun s ↦
        CommRingCat.ofHom ((descAux s).comp
          (ULift.ringEquiv : ULift.{v}
            (Ring.DirectLimit
              (fun i ↦ ↑(G.obj i))
              (fun i j h ↦ (G.map (homOfLE h)).hom)) ≃+*
                Ring.DirectLimit
                  (fun i ↦ ↑(G.obj i))
                  (fun i j h ↦ (G.map (homOfLE h)).hom)).toRingHom)
      fac := ?_
      uniq := ?_ }
  · intro s i
    apply CommRingCat.hom_ext
    ext x
    cases x using ULift.casesOn
    rename_i x
    change
      (descAux s)
          (Ring.DirectLimit.of
            (fun i ↦ ↑(G.obj i))
            (fun i j h ↦ (G.map (homOfLE h)).hom)
            i x) =
        (s.ι.app i).hom (ULift.up x)
    simp only [descAux, RingHom.comp_apply, Ring.DirectLimit.lift_of]
    rfl
  · intro s m hm
    apply CommRingCat.hom_ext
    ext x
    cases x using ULift.casesOn
    rename_i x
    induction x using Ring.DirectLimit.induction_on with
    | ih i x =>
        -- Proof comment: every direct-limit class is represented at some stage, and the cocone
        -- relation fixes the value of any candidate desc map on that representative.
        have hm' :
            (((directed_commRing_directLimitCocone (A₀ := A₀) G).ι.app i) ≫ m).hom
                (ULift.up x) =
              (s.ι.app i).hom (ULift.up x) := by
          simpa using congrArg
            (fun f : (directed_commAlg_toULiftCommRing (A₀ := A₀) G).obj i ⟶ s.pt ↦
              f.hom (ULift.up x))
            (hm i)
        change
          (m.hom)
              (ULift.up
                (Ring.DirectLimit.of
                  (fun i ↦ ↑(G.obj i))
                  (fun i j h ↦ (G.map (homOfLE h)).hom)
                  i x)) =
            (descAux s)
              (Ring.DirectLimit.of
                (fun i ↦ ↑(G.obj i))
                (fun i j h ↦ (G.map (homOfLE h)).hom)
                i x)
        simpa [descAux, Ring.DirectLimit.lift_of] using hm'

/-- Helper for Lemma 10.168.5: the stage maps from the explicit ring direct limit to the cocone
point agree with the given cocone legs. -/
theorem directed_commAlg_ringDirectLimit_leg_compatible
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G)
    {i j : I} (h : i ≤ j) :
    ((c.cocone.ι.app j).hom.toRingHom : G.obj j →+* c.cocone.pt).comp
        (G.map (homOfLE h)).hom.toRingHom =
      (c.cocone.ι.app i).hom.toRingHom := by
  -- Proof comment: this is exactly the cocone naturality relation, read on the underlying ring
  -- homomorphisms.
  exact congrArg (fun f : G.obj i ⟶ c.cocone.pt ↦ f.hom.toRingHom) (c.cocone.w (homOfLE h))

/-- Helper for Lemma 10.168.5: the explicit ring direct limit maps canonically to the chosen
colimit point by the cocone legs. -/
noncomputable def directed_commAlg_ringDirectLimitToCoconePoint
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G) :
    Ring.DirectLimit
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom) →+* ↑c.cocone.pt :=
  Ring.DirectLimit.lift
    (fun i ↦ ↑(G.obj i))
    (fun i j h ↦ (G.map (homOfLE h)).hom)
    ↑c.cocone.pt
    (fun i ↦ (c.cocone.ι.app i).hom.toRingHom)
    (fun _ _ h x ↦
      DFunLike.congr_fun (directed_commAlg_ringDirectLimit_leg_compatible (G := G) (c := c) h) x)

/-- Helper for Lemma 10.168.5: the canonical map from the explicit ring direct limit to the
cocone point agrees with the stage cocone legs. -/
theorem directed_commAlg_ringDirectLimitToCoconePoint_comp_of
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G) (i : I) :
    (directed_commAlg_ringDirectLimitToCoconePoint (G := G) c).comp
        (Ring.DirectLimit.of
          (fun i ↦ ↑(G.obj i))
          (fun i j h ↦ (G.map (homOfLE h)).hom) i) =
      (c.cocone.ι.app i).hom.toRingHom := by
  -- Proof comment: evaluate the direct-limit lift on the class of a stage element.
  ext x
  simp [directed_commAlg_ringDirectLimitToCoconePoint, RingHom.comp_apply, Ring.DirectLimit.lift_of]

/-- Helper for Lemma 10.168.5: the explicit ring direct limit of a directed diagram of
`A₀`-algebras. -/
abbrev directed_commAlg_ringDirectLimit
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) :=
  Ring.DirectLimit
    (fun i ↦ ↑(G.obj i))
    (fun i j h ↦ (G.map (homOfLE h)).hom)

/-- Helper for Lemma 10.168.5: the explicit ring direct limit carries the canonical `A₀`-algebra
structure induced from an arbitrary stage. -/
@[reducible]
noncomputable instance directed_commAlg_ringDirectLimitAlgebra
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) :
    Algebra A₀ (directed_commAlg_ringDirectLimit (A₀ := A₀) G) :=
  let i : I := Classical.arbitrary I
  ((Ring.DirectLimit.of
      (fun i ↦ ↑(G.obj i))
      (fun i j h ↦ (G.map (homOfLE h)).hom)
      i).comp
    (algebraMap A₀ ↑(G.obj i))).toAlgebra

/-- Helper for Lemma 10.168.5: the canonical algebra map into the explicit ring direct limit agrees
with the map induced from any fixed stage. -/
theorem directed_ringDirectLimit_algebraMap_eq_of
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (i : I) (a : A₀) :
    algebraMap A₀ (directed_commAlg_ringDirectLimit (A₀ := A₀) G) a =
      Ring.DirectLimit.of
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        i (algebraMap A₀ ↑(G.obj i) a) := by
  classical
  let i₀ : I := Classical.arbitrary I
  obtain ⟨j, hi₀j, hij⟩ := exists_ge_ge i₀ i
  change
    Ring.DirectLimit.of
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        i₀ (algebraMap A₀ ↑(G.obj i₀) a) =
      Ring.DirectLimit.of
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        i (algebraMap A₀ ↑(G.obj i) a)
  calc
    Ring.DirectLimit.of
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        i₀ (algebraMap A₀ ↑(G.obj i₀) a) =
      Ring.DirectLimit.of
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        j (((G.map (homOfLE hi₀j)).hom) (algebraMap A₀ ↑(G.obj i₀) a)) := by
          symm
          exact Ring.DirectLimit.of_f
            (G := fun i ↦ ↑(G.obj i))
            (f := fun i j h ↦ (G.map (homOfLE h)).hom)
            (i := i₀) (j := j) (hij := hi₀j) (x := algebraMap A₀ ↑(G.obj i₀) a)
    _ =
      Ring.DirectLimit.of
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        j (algebraMap A₀ ↑(G.obj j) a) := by
          rw [(G.map (homOfLE hi₀j)).hom.commutes]
    _ =
      Ring.DirectLimit.of
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        j (((G.map (homOfLE hij)).hom) (algebraMap A₀ ↑(G.obj i) a)) := by
          rw [← (G.map (homOfLE hij)).hom.commutes]
    _ =
      Ring.DirectLimit.of
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        i (algebraMap A₀ ↑(G.obj i) a) := by
          exact Ring.DirectLimit.of_f
            (G := fun i ↦ ↑(G.obj i))
            (f := fun i j h ↦ (G.map (homOfLE h)).hom)
            (i := i) (j := j) (hij := hij) (x := algebraMap A₀ ↑(G.obj i) a)

/-- Helper for Lemma 10.168.5: each stage maps canonically to the explicit ring direct limit as an
`A₀`-algebra. -/
noncomputable abbrev directed_commAlg_stageToRingDirectLimitAlgHom
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (i : I) :
    ↑(G.obj i) →ₐ[A₀] directed_commAlg_ringDirectLimit (A₀ := A₀) G :=
  { toRingHom :=
      Ring.DirectLimit.of
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        i
    commutes' := fun a ↦ (directed_ringDirectLimit_algebraMap_eq_of (A₀ := A₀) G i a).symm }

/-- Helper for Lemma 10.168.5: the canonical map from the explicit ring direct limit to the cocone
point is an `A₀`-algebra map. -/
noncomputable abbrev directed_commAlg_ringDirectLimitToCoconePointAlgHom
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G) :
    directed_commAlg_ringDirectLimit (A₀ := A₀) G →ₐ[A₀] ↑c.cocone.pt :=
  { toRingHom := directed_commAlg_ringDirectLimitToCoconePoint (A₀ := A₀) G c
    commutes' := fun a ↦ by
      classical
      let i : I := Classical.arbitrary I
      have hstage :
          directed_commAlg_ringDirectLimitToCoconePoint (A₀ := A₀) G c
              (algebraMap A₀ (directed_commAlg_ringDirectLimit (A₀ := A₀) G) a) =
            (c.cocone.ι.app i).hom (algebraMap A₀ ↑(G.obj i) a) := by
        rw [directed_ringDirectLimit_algebraMap_eq_of (A₀ := A₀) G i]
        simpa [RingHom.comp_apply] using congrArg
          (fun f : ↑(G.obj i) →+* ↑c.cocone.pt ↦
            f (algebraMap A₀ ↑(G.obj i) a))
          (directed_commAlg_ringDirectLimitToCoconePoint_comp_of (A₀ := A₀) G c i)
      exact hstage.trans <| by
        simpa using (c.cocone.ι.app i).hom.commutes a }

/-- Helper for Lemma 10.168.5: the canonical map from the explicit ring direct limit to the chosen
cocone point agrees with the given cocone leg on every stage class. -/
theorem directed_commAlg_ringDirectLimitToCoconePointAlgHom_comp_of
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (c : ColimitCocone G) (i : I) (x : ↑(G.obj i)) :
    directed_commAlg_ringDirectLimitToCoconePointAlgHom (A₀ := A₀) G c
        (Ring.DirectLimit.of
          (fun i ↦ ↑(G.obj i))
          (fun i j h ↦ (G.map (homOfLE h)).hom)
          i x) =
      (c.cocone.ι.app i).hom x := by
  -- Proof comment: evaluate the direct-limit lift on the class represented at stage `i`.
  exact congrArg (fun f : _ →+* ↑c.cocone.pt ↦ f x)
    (directed_commAlg_ringDirectLimitToCoconePoint_comp_of (A₀ := A₀) G c i)

/-- Helper for Lemma 10.168.5: a finite family of indices in a directed preorder has a common
upper bound. -/
theorem directed_finset_common_upper_bound
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (s : Finset I) :
    ∃ i : I, ∀ j ∈ s, j ≤ i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨Classical.arbitrary I, ?_⟩
      intro j hj
      exact False.elim (Finset.notMem_empty j hj)
  | insert a s ha hs =>
      rcases hs with ⟨i, hi⟩
      rcases exists_ge_ge a i with ⟨k, hak, hik⟩
      refine ⟨k, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · exact hak
      · exact (hi j hj').trans hik

/-- Helper for Lemma 10.168.5: a finite indexed family of stage witnesses can be merged to one
common stage. -/
theorem directed_fin_common_upper_bound
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    {n : ℕ} (u : Fin n → I) :
    ∃ i : I, ∀ k : Fin n, u k ≤ i := by
  classical
  obtain ⟨i, hi⟩ := directed_finset_common_upper_bound (s := Finset.univ.image u)
  refine ⟨i, ?_⟩
  intro k
  exact hi (u k) (Finset.mem_image_of_mem u (Finset.mem_univ k))

/-- Helper for Lemma 10.168.5: the legs of any cocone over a directed diagram of `A₀`-algebras
commute with the transition maps on the underlying rings. -/
theorem directed_commAlg_cocone_leg_compatible
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (t : Cocone G)
    {i j : I} (h : i ≤ j) :
    ((t.ι.app j).hom.toRingHom : ↑(G.obj j) →+* ↑t.pt).comp (G.map (homOfLE h)).hom.toRingHom =
      (t.ι.app i).hom.toRingHom := by
  -- Proof comment: this is just cocone naturality read on the underlying ring homomorphisms.
  exact congrArg (fun f : G.obj i ⟶ t.pt ↦ f.hom.toRingHom) (t.w (homOfLE h))

/-- Helper for Lemma 10.168.5: every cocone over a directed diagram of `A₀`-algebras receives the
canonical algebra map from the explicit `Ring.DirectLimit`. -/
noncomputable abbrev directed_commAlg_ringDirectLimitDescAlgHom
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (t : Cocone G) :
    directed_commAlg_ringDirectLimit (A₀ := A₀) G →ₐ[A₀] ↑t.pt :=
  { toRingHom :=
      Ring.DirectLimit.lift
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        ↑t.pt
        (fun i ↦ (t.ι.app i).hom.toRingHom)
        (fun _ _ h x ↦
          DFunLike.congr_fun (directed_commAlg_cocone_leg_compatible (A₀ := A₀) G t h) x)
    commutes' := fun a ↦ by
      classical
      let i : I := Classical.arbitrary I
      -- Proof comment: check the `A₀`-algebra structure on one stage representative and then
      -- descend it to the direct limit.
      rw [directed_ringDirectLimit_algebraMap_eq_of (A₀ := A₀) G i]
      change
        Ring.DirectLimit.lift
            (fun i ↦ ↑(G.obj i))
            (fun i j h ↦ (G.map (homOfLE h)).hom)
            ↑t.pt
            (fun i ↦ (t.ι.app i).hom.toRingHom)
            (fun _ _ h x ↦
              DFunLike.congr_fun
                (directed_commAlg_cocone_leg_compatible (A₀ := A₀) G t h) x)
            (Ring.DirectLimit.of
              (fun i ↦ ↑(G.obj i))
              (fun i j h ↦ (G.map (homOfLE h)).hom)
              i (algebraMap A₀ ↑(G.obj i) a)) =
          algebraMap A₀ ↑t.pt a
      simpa [RingHom.comp_apply, Ring.DirectLimit.lift_of] using (t.ι.app i).hom.commutes a }

/-- Helper for Lemma 10.168.5: the canonical desc map from the explicit `Ring.DirectLimit`
evaluates on a stage class by the corresponding cocone leg. -/
@[simp]
theorem directed_commAlg_ringDirectLimitDescAlgHom_comp_of
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) (t : Cocone G) (i : I) (x : ↑(G.obj i)) :
    directed_commAlg_ringDirectLimitDescAlgHom (A₀ := A₀) G t
        (Ring.DirectLimit.of
          (fun i ↦ ↑(G.obj i))
          (fun i j h ↦ (G.map (homOfLE h)).hom)
          i x) =
      (t.ι.app i).hom x := by
  -- Proof comment: this is exactly the defining evaluation formula of `Ring.DirectLimit.lift`.
  change
    Ring.DirectLimit.lift
        (fun i ↦ ↑(G.obj i))
        (fun i j h ↦ (G.map (homOfLE h)).hom)
        ↑t.pt
        (fun i ↦ (t.ι.app i).hom.toRingHom)
        (fun _ _ h x ↦
          DFunLike.congr_fun
            (directed_commAlg_cocone_leg_compatible (A₀ := A₀) G t h) x)
        (Ring.DirectLimit.of
          (fun i ↦ ↑(G.obj i))
          (fun i j h ↦ (G.map (homOfLE h)).hom)
          i x) =
      (t.ι.app i).hom x
  simp only [Ring.DirectLimit.lift_of]
  rfl

/-- Helper for Chap10 Lemma 10 168 5: the explicit direct-limit stage algebra maps are natural
with respect to the transition maps of a directed `CommAlgCat` diagram. -/
theorem directed_commAlg_stageToRingDirectLimitAlgHom_naturality
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (G : I ⥤ CommAlgCat.{u} A₀) {i j : I} (h : i ≤ j) :
    (directed_commAlg_stageToRingDirectLimitAlgHom (A₀ := A₀) G j).comp
        (G.map (homOfLE h)).hom =
      directed_commAlg_stageToRingDirectLimitAlgHom (A₀ := A₀) G i := by
  -- Proof comment: the naturality equation is exactly the defining relation of the explicit
  -- `Ring.DirectLimit` quotient, with the algebra-map wrappers stripped off by extensionality.
  ext x
  exact
    (Ring.DirectLimit.of_f
      (G := fun i ↦ ↑(G.obj i))
      (f := fun i j h ↦ (G.map (homOfLE h)).hom)
      (i := i) (j := j) (hij := h) (x := x))

end
