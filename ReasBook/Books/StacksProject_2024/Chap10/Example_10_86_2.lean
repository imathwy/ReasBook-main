import Mathlib
import stacks_project.Chap10.Definition_10_86_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

variable {I : Type u} [Preorder I]
variable {R : Type v} [Ring R]

namespace CategoryTheory.Functor

variable (A : OrderDual I ⥤ ModuleCat R)

/-- The stable image at a stage of a module-valued inverse system:
`A'_i = ⋂_{j ≥ i} im(A_j → A_i)`. This is the `ModuleCat` realization of the owner notion
`Functor.eventualRange`. -/
def stableImage (i : OrderDual I) : Submodule R (A.obj i) :=
  ⨅ (j : OrderDual I) (_f : j ⟶ i), LinearMap.range (A.map _f).hom

theorem mem_stableImage_iff {i : OrderDual I} {x : A.obj i} :
    x ∈ A.stableImage i ↔ x ∈ (A ⋙ forget (ModuleCat R)).eventualRange i := by
  change x ∈ (⨅ (j : OrderDual I) (f : j ⟶ i), LinearMap.range (A.map f).hom) ↔
      x ∈ ⋂ (j : OrderDual I) (f : j ⟶ i), Set.range (A.map f)
  simp

variable [IsDirectedOrder I]

private theorem stableImage_mapsTo {i j : OrderDual I} (f : j ⟶ i) :
    Set.MapsTo (A.map f) (A.stableImage j) (A.stableImage i) := by
  intro x hx
  exact (A.mem_stableImage_iff.2 <|
    (A ⋙ forget (ModuleCat R)).eventualRange_mapsTo f <|
      A.mem_stableImage_iff.1 hx)

/-- The module-valued stable-image subsystem attached to `A`, obtained by replacing each stage by
its stable image. This is the `ModuleCat` bridge over the owner functor
`(A ⋙ forget (ModuleCat R)).toEventualRanges`. -/
@[simps]
def stableImageSystem : OrderDual I ⥤ ModuleCat R where
  obj i := ModuleCat.of R (A.stableImage i)
  map f := ModuleCat.ofHom <|
    (((A.map f).hom.domRestrict (A.stableImage _)).codRestrict
      (A.stableImage _) fun x ↦ A.stableImage_mapsTo f x.2)
  map_id i := by
    ext x
    simp
  map_comp f g := by
    ext x
    simp

/-- The stable-image subsystem sits canonically inside the original inverse system. -/
@[simps]
def stableImageι : A.stableImageSystem ⟶ A where
  app i := ModuleCat.ofHom (A.stableImage i).subtype
  naturality f := by
    intro Y g
    apply ModuleCat.hom_ext
    ext x
    rfl

theorem surjective_stableImageSystem
    (hML : (A ⋙ forget (ModuleCat R)).IsMittagLeffler) {i j : OrderDual I} (f : j ⟶ i) :
    Function.Surjective (A.stableImageSystem.map f) := by
  intro x
  obtain ⟨y, hy, hyx⟩ :=
    hML.subset_image_eventualRange (A ⋙ forget (ModuleCat R)) f <|
      (A.mem_stableImage_iff.1 x.2)
  refine ⟨⟨y, A.mem_stableImage_iff.2 hy⟩, ?_⟩
  exact Subtype.ext hyx

private def stableImageCone : Cone A.stableImageSystem where
  pt := limit A
  π :=
    { app := fun i ↦
        ModuleCat.ofHom <|
          ((limit.π A i).hom.codRestrict (A.stableImage i) fun x ↦ by
            have hx : (limit.π A i).hom x ∈ (A ⋙ forget (ModuleCat R)).eventualRange i := by
              change (ModuleCat.Hom.hom (limit.π A i)) x ∈
                  ⋂ (j : OrderDual I) (f : j ⟶ i), Set.range (A.map f)
              simp only [Set.mem_iInter]
              intro j f
              refine ⟨(limit.π A j).hom x, ?_⟩
              exact congrArg (fun g ↦ g.hom x) (limit.w A f)
            exact A.mem_stableImage_iff.2 hx)
      naturality := fun f ↦ by
        intro Y g
        apply ModuleCat.hom_ext
        ext x
        apply Subtype.ext
        exact (congrArg (fun h ↦ h.hom x) (limit.w A g)).symm }

/-- The inverse limit of `A` is unchanged when we replace each stage by its stable image. -/
def limitIsoStableImageSystem :
    limit A ≅ limit A.stableImageSystem where
  hom := limit.lift _ A.stableImageCone
  inv := limMap A.stableImageι
  hom_inv_id := by
    apply limit.hom_ext
    intro i
    erw [Category.assoc, limMap_π, ← Category.assoc, limit.lift_π]
    apply ModuleCat.hom_ext
    rfl
  inv_hom_id := by
    apply limit.hom_ext
    intro i
    erw [Category.assoc, limit.lift_π]
    apply ModuleCat.hom_ext
    ext x
    apply Subtype.ext
    exact congrArg (fun h ↦ h.hom x) (limMap_π A.stableImageι i)

end CategoryTheory.Functor

variable [IsDirectedOrder I]

omit [IsDirectedOrder I] in
-- Proof sketch: this is the module-valued specialization of the owner theorem
-- `Functor.isMittagLeffler_of_surjective` for the underlying `Type`-valued inverse system.
/-- Example 10.86.2 (first direction): if all transition maps in a directed inverse system of
`R`-modules are surjective, then the underlying inverse system is Mittag-Leffler. -/
theorem isMittagLeffler_of_surjective
    (A : OrderDual I ⥤ ModuleCat R)
    (hSurj : ∀ ⦃i j : I⦄ (hij : i ≤ j), Function.Surjective (A.map (homOfLE hij))) :
    (A ⋙ forget (ModuleCat R)).IsMittagLeffler := by
  refine Functor.isMittagLeffler_of_surjective (A ⋙ forget (ModuleCat R)) ?_
  intro j i f
  simpa using hSurj (leOfHom f)

-- Proof sketch: replace each stage by the stable image of sufficiently far transition maps into
-- that stage. Mathlib packages these stable images as eventual ranges; the corresponding
-- `ModuleCat` stable-image subsystem has surjective transition maps by the Mittag-Leffler
-- condition and the same inverse limit by the universal property of the limit.
/-- Example 10.86.2: replacing a module-valued inverse system by its stable-image replacement
`A'_i = ⋂_{j ≥ i} im(A_j → A_i)` does not change the inverse limit. The Mittag-Leffler hypothesis
is only needed for the surjectivity companion
`surjective_stableImageReplacement_of_isMittagLeffler`. -/
def stableImageReplacement_limitIso (A : OrderDual I ⥤ ModuleCat R) :
    limit A ≅ limit A.stableImageSystem :=
  A.limitIsoStableImageSystem

/-- Companion to Example 10.86.2: the Mittag-Leffler hypothesis makes the transition maps in the
stable-image replacement surjective. -/
theorem surjective_stableImageReplacement_of_isMittagLeffler
    (A : OrderDual I ⥤ ModuleCat R) (hML : (A ⋙ forget (ModuleCat R)).IsMittagLeffler) :
    ∀ ⦃i j : I⦄ (hij : i ≤ j),
      Function.Surjective (A.stableImageSystem.map (homOfLE hij)) := by
  intro i j hij
  simpa using A.surjective_stableImageSystem hML (homOfLE hij)
