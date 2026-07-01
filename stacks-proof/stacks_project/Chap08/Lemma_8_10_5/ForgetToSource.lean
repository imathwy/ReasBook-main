import stacks_project.Chap08.Definition_8_2_2
import stacks_project.Chap08.Definition_8_3_5
import stacks_project.Chap08.Definition_8_5_5
import stacks_project.Chap04.Lemma_4_33_3
import stacks_project.Chap04.Lemma_4_33_8
import stacks_project.Chap08.Lemma_8_4_2
import stacks_project.Chap08.Lemma_8_4_4

universe uC uX vC vX

namespace CategoryTheory

open FibredCategoryMor
open Functor IsStronglyCartesian
open StackInGroupoidsOver.Hom

section

variable {C : Type uC} [Category.{vC} C]
variable {J : GrothendieckTopology C}
variable {Xₛ Yₛ : StackInGroupoidsOver J}

/-- Helper for Lemma 8.10.5: an object in the `G F`-fiber over `y` has an underlying source
object in the fiber of `Xₛ.p` over the same downstairs base object. -/
noncomputable def inherited_source_fiber_obj
    (F : Xₛ ⟶ Yₛ) {y : Yₛ.S} (x : (G F).Fiber y) :
    Xₛ.p.Fiber (Yₛ.p.obj y) :=
  -- Forget the target label `y`; the base equality is exactly the compatibility
  -- `Xₛ.p = G F ⋙ Yₛ.p`.
  Functor.Fiber.mk (a := x.1) <|
    let hcomm :
        Yₛ.p.obj ((G F).obj x.1) = Xₛ.p.obj x.1 := by
          simpa using congrArg (fun H ↦ H.obj x.1) (StackInGroupoidsOver.Hom.comm F)
    hcomm.symm.trans (congrArg Yₛ.p.obj x.2)

/-- Helper for Lemma 8.10.5: forgetting the target label on a source-fiber object preserves the
downstairs base object. -/
private theorem inherited_source_fiber_obj_base
    (F : Xₛ ⟶ Yₛ) {y : Yₛ.S} (x : (G F).Fiber y) :
    Xₛ.p.obj x.1 = Yₛ.p.obj y := by
  -- This is exactly the base equality stored by `inherited_source_fiber_obj`.
  simpa using (inherited_source_fiber_obj (F := F) x).2

/-- Helper for Lemma 8.10.5: after applying `Yₛ.p`, a morphism in the `G F`-fiber over `y`
has the expected conjugated identity base map. -/
private theorem inherited_source_fiber_hom_target_base_eq_id
    (F : Xₛ ⟶ Yₛ) {y : Yₛ.S} {x₁ x₂ : (G F).Fiber y} (φ : x₁ ⟶ x₂) :
    Yₛ.p.map ((G F).map φ.1) =
      eqToHom (congrArg Yₛ.p.obj x₁.2) ≫
        𝟙 (Yₛ.p.obj y) ≫
        eqToHom (congrArg Yₛ.p.obj x₂.2).symm := by
  letI : (G F).IsHomLift (𝟙 y) φ.1 := φ.2
  have hφFiber :
      (G F).map φ.1 =
        eqToHom (IsHomLift.domain_eq (G F) (𝟙 y) φ.1) ≫
          𝟙 y ≫
          eqToHom (IsHomLift.codomain_eq (G F) (𝟙 y) φ.1).symm := by
    -- Read the fiber morphism over `y` through the owner `IsHomLift.fac'` normalization.
    simpa using (IsHomLift.fac' (G F) (𝟙 y) φ.1)
  -- Applying `Yₛ.p` transports the fiber identity to the downstairs identity on `Yₛ.p.obj y`.
  simpa [Functor.map_comp, eqToHom_map, Category.assoc] using congrArg Yₛ.p.map hφFiber

/-- Helper for Lemma 8.10.5: a morphism in a `G F`-fiber is vertical for the downstairs
projection `Xₛ.p` over the corresponding base identity. -/
theorem inherited_source_fiber_hom_isHomLift
    (F : Xₛ ⟶ Yₛ) {y : Yₛ.S} {x₁ x₂ : (G F).Fiber y} (φ : x₁ ⟶ x₂) :
    Xₛ.p.IsHomLift (𝟙 (Yₛ.p.obj y)) φ.1 := by
  -- Route correction: first interpret the fiber morphism as a vertical map in the target stack,
  -- then transport that same base identity back across the based functor underlying `F`.
  have hφY : Yₛ.p.IsHomLift (𝟙 (Yₛ.p.obj y)) ((G F).map φ.1) := by
    refine IsHomLift.of_fac' Yₛ.p (𝟙 (Yₛ.p.obj y)) ((G F).map φ.1)
      (congrArg Yₛ.p.obj x₁.2) (congrArg Yₛ.p.obj x₂.2) ?_
    -- Reuse the owner-normalized fiber identity before transporting it back across `F`.
    exact inherited_source_fiber_hom_target_base_eq_id (F := F) φ
  -- The based-functor compatibility of `F` identifies lifts in `Xₛ` with lifts of their images.
  exact ((toBasedFunctor F).isHomLift_iff (𝟙 (Yₛ.p.obj y)) φ.1).1 hφY

/-- Helper for Lemma 8.10.5: forgetting the target label on one `G F`-fiber yields the
corresponding fiber of the source projection `Xₛ.p`. This is the componentwise input for the
eventual descent-data forgetting functor. -/
noncomputable def inherited_source_fiber_forget
    (F : Xₛ ⟶ Yₛ) (y : Yₛ.S) :
    (G F).Fiber y ⥤ Xₛ.p.Fiber (Yₛ.p.obj y) where
  obj x := inherited_source_fiber_obj (F := F) x
  map φ :=
    -- Package the underlying total-category morphism with the verticality proved just above.
    letI := inherited_source_fiber_hom_isHomLift (F := F) φ
    Functor.Fiber.homMk Xₛ.p (Yₛ.p.obj y) φ.1
  map_id x := by
    -- After forgetting to the total category, both sides are the same identity morphism.
    apply Functor.Fiber.hom_ext
    rfl
  map_comp φ ψ := by
    -- After forgetting to the total category, both sides are the same composite morphism.
    apply Functor.Fiber.hom_ext
    rfl

/-- Helper for Lemma 8.10.5: the forgotten canonical pullback arrow in `(G F)` is already
strongly cartesian for `Xₛ.p` over the downstairs arrow `Yₛ.p.map f`. -/
theorem inherited_source_pullback_lift_isStronglyCartesian
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {yi Z : Yₛ.S} (f : Z ⟶ yi) (x : (G F).Fiber yi) :
    Xₛ.p.IsStronglyCartesian (Yₛ.p.map f) ((canonicalPullbackChoice (G F)).map f x) := by
  let hcGF := canonicalPullbackChoice (G F)
  let φ := hcGF.map f x
  let xPullGF : (G F).Fiber Z :=
    (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x)
  have hφX : Xₛ.p.IsHomLift (Yₛ.p.map f) φ := by
    -- First push the owner lift in `(G F)` down to `Yₛ.p`, then pull it back across `F`.
    have hφY : Yₛ.p.IsHomLift (Yₛ.p.map f) ((G F).map φ) := by
      have hφGF : (G F).IsHomLift f φ :=
        (hcGF.isStronglyCartesian f x).toIsHomLift
      letI : (G F).IsHomLift f φ := hφGF
      refine IsHomLift.of_fac' Yₛ.p (Yₛ.p.map f) ((G F).map φ)
        (congrArg Yₛ.p.obj xPullGF.2) (congrArg Yₛ.p.obj x.2) ?_
      have hφFiber :
          (G F).map φ = eqToHom xPullGF.2 ≫ f ≫ eqToHom x.2.symm := by
        -- The chosen pullback arrow in `(G F)` is the canonical lift of `f`.
        simpa [φ, xPullGF] using (IsHomLift.fac' (G F) f φ)
      calc
        Yₛ.p.map ((G F).map φ)
            = Yₛ.p.map (eqToHom xPullGF.2 ≫ f ≫ eqToHom x.2.symm) := by
                exact congrArg Yₛ.p.map hφFiber
        _ = Yₛ.p.map (eqToHom xPullGF.2) ≫ Yₛ.p.map f ≫ Yₛ.p.map (eqToHom x.2.symm) := by
              simp [Functor.map_comp, Category.assoc]
        _ =
            eqToHom (congrArg Yₛ.p.obj xPullGF.2) ≫ Yₛ.p.map f ≫
              eqToHom (congrArg Yₛ.p.obj x.2).symm := by
                simp [eqToHom_map]
    exact ((toBasedFunctor F).isHomLift_iff (Yₛ.p.map f) φ).1 hφY
  have hφOwner : Xₛ.p.IsStronglyCartesian (Xₛ.p.map φ) φ := by
    -- Every morphism in the source stack is strongly cartesian over its own base map.
    exact (inferInstance : IsFibredInGroupoids Xₛ.p).isStronglyCartesian_map φ
  letI : Xₛ.p.IsHomLift (Yₛ.p.map f) φ := hφX
  letI : Xₛ.p.IsStronglyCartesian (Xₛ.p.map φ) φ := hφOwner
  -- Rebase the owner strong-cartesian structure along the explicit external lift.
  exact
    BasedFunctor.isStronglyCartesian_of_external_hom_lift
      (p := Xₛ.p) (f := Yₛ.p.map f) (φ := φ)

/-- Helper for Lemma 8.10.5: the forgotten source object of the `G F`-pullback is compared with
the canonical downstairs pullback in `Xₛ`. -/
noncomputable def inherited_source_pullback_comparison
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {yi Z : Yₛ.S} (f : Z ⟶ yi) (x : (G F).Fiber yi) :
    inherited_source_fiber_obj (F := F)
        (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x) ≅
      (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f).op.toLoc).toFunctor.obj
        (inherited_source_fiber_obj (F := F) x)) :=
  let hcGF := canonicalPullbackChoice (G F)
  let hcX := canonicalPullbackChoice Xₛ.p
  let xPullGF : (G F).Fiber Z :=
    (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x)
  let xPullX :
      Xₛ.p.Fiber (Yₛ.p.obj Z) :=
    (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f).op.toLoc).toFunctor.obj
      (inherited_source_fiber_obj (F := F) x))
  let ψ :
      (inherited_source_fiber_obj (F := F) xPullGF).1 ⟶
        (inherited_source_fiber_obj (F := F) x).1 :=
    hcGF.map f x
  let φ :
      xPullX.1 ⟶ (inherited_source_fiber_obj (F := F) x).1 :=
    hcX.map (Yₛ.p.map f) (inherited_source_fiber_obj (F := F) x)
  have hφ : Xₛ.p.IsStronglyCartesian (Yₛ.p.map f) φ :=
    hcX.isStronglyCartesian (Yₛ.p.map f) (inherited_source_fiber_obj (F := F) x)
  have hψ : Xₛ.p.IsStronglyCartesian (Yₛ.p.map f) ψ :=
    inherited_source_pullback_lift_isStronglyCartesian
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x
  have hf : Yₛ.p.map f = (Iso.refl (Yₛ.p.obj Z)).hom ≫ Yₛ.p.map f := by
    simp
  let e :
      (inherited_source_fiber_obj (F := F) xPullGF).1 ≅ xPullX.1 :=
    Functor.IsStronglyCartesian.domainIsoOfBaseIso Xₛ.p hf φ ψ
  letI : Xₛ.p.IsHomLift (𝟙 (Yₛ.p.obj Z)) e.hom := by
    -- The comparison map between the two pullback domains is vertical over `Yₛ.p.obj Z`.
    change Xₛ.p.IsHomLift (Iso.refl (Yₛ.p.obj Z)).hom e.hom
    exact Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift Xₛ.p hf φ ψ
  letI : Xₛ.p.IsHomLift (𝟙 (Yₛ.p.obj Z)) e.inv := by
    -- The inverse comparison map is vertical for the same base identity.
    change Xₛ.p.IsHomLift (Iso.refl (Yₛ.p.obj Z)).inv e.inv
    exact Functor.IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift Xₛ.p hf φ ψ
  -- Package the owner comparison isomorphism as an isomorphism in the fiber over `Yₛ.p.obj Z`.
  { hom := Functor.Fiber.homMk Xₛ.p (Yₛ.p.obj Z) e.hom
    inv := Functor.Fiber.homMk Xₛ.p (Yₛ.p.obj Z) e.inv
    hom_inv_id := by
      apply Functor.Fiber.hom_ext
      change e.hom ≫ e.inv = 𝟙 _
      exact e.hom_inv_id
    inv_hom_id := by
      apply Functor.Fiber.hom_ext
      change e.inv ≫ e.hom = 𝟙 _
      exact e.inv_hom_id }

/-- Helper for Lemma 8.10.5: postcomposing the pullback-comparison hom with the chosen downstairs
pullback arrow in `Xₛ` recovers the chosen pullback arrow in `(G F)`. -/
theorem inherited_source_pullback_comparison_hom_postcompose
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {yi Z : Yₛ.S} (f : Z ⟶ yi) (x : (G F).Fiber yi) :
    (inherited_source_pullback_comparison (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x).hom.1 ≫
        (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f) (inherited_source_fiber_obj (F := F) x) =
      (canonicalPullbackChoice (G F)).map f x := by
  let hcGF := canonicalPullbackChoice (G F)
  let hcX := canonicalPullbackChoice Xₛ.p
  let xPullGF : (G F).Fiber Z :=
    (((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.obj x)
  let xPullX :
      Xₛ.p.Fiber (Yₛ.p.obj Z) :=
    (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f).op.toLoc).toFunctor.obj
      (inherited_source_fiber_obj (F := F) x))
  let ψ :
      (inherited_source_fiber_obj (F := F) xPullGF).1 ⟶
        (inherited_source_fiber_obj (F := F) x).1 :=
    hcGF.map f x
  let φ :
      xPullX.1 ⟶ (inherited_source_fiber_obj (F := F) x).1 :=
    hcX.map (Yₛ.p.map f) (inherited_source_fiber_obj (F := F) x)
  have hφ : Xₛ.p.IsStronglyCartesian (Yₛ.p.map f) φ :=
    hcX.isStronglyCartesian (Yₛ.p.map f) (inherited_source_fiber_obj (F := F) x)
  have hψ : Xₛ.p.IsStronglyCartesian (Yₛ.p.map f) ψ :=
    inherited_source_pullback_lift_isStronglyCartesian
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x
  have hf : Yₛ.p.map f = (Iso.refl (Yₛ.p.obj Z)).hom ≫ Yₛ.p.map f := by
    simp
  -- Unfold the comparison only to the owner-level `domainIsoOfBaseIso` normal form.
  dsimp [inherited_source_pullback_comparison]
  change (Functor.IsStronglyCartesian.domainIsoOfBaseIso Xₛ.p hf φ ψ).hom ≫ φ = ψ
  rw [Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom]
  exact Functor.IsStronglyCartesian.fac Xₛ.p (Yₛ.p.map f) φ hf ψ

end

end CategoryTheory
