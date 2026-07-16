import StacksProject_2024.stacks_project.Chap22.Definition_22_26_2
import StacksProject_2024.stacks_project.Chap22.Definition_22_26_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v w

namespace DifferentialGradedCategory

variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w}
variable [DA : DifferentialGradedCategory R A] [DB : DifferentialGradedCategory R B]

namespace DgFunctor

local notation "DGFunctor" => DgFunctor R A B

/-- A DG functor preserves closed degree-`0` morphisms. -/
theorem mapCompHom_closed (F : DGFunctor) {X Y : A} (f : CompHom X Y) :
    DB.d 0 (F.map f.val) = 0 := by
  calc
    DB.d 0 (F.map f.val) = F.map (DA.d 0 f.val) := by
      symm
      exact F.map_d f.val
    _ = F.map 0 := by rw [f.closed]
    _ = 0 := by simpa using (F.map_zero 1 : F.map (0 : X ⟶[1] Y) = 0)

/-- The action of a DG functor on closed degree-`0` morphisms. -/
def mapCompHom (F : DGFunctor) {X Y : A} (f : CompHom X Y) :
    CompHom (F.obj X) (F.obj Y) :=
  ⟨F.map f.val, mapCompHom_closed F f⟩

/-- The underlying degree-`0` morphism of `mapCompHom`. -/
@[simp] theorem mapCompHom_val (F : DGFunctor) {X Y : A} (f : CompHom X Y) :
    (mapCompHom F f).val = F.map f.val := rfl

/-- A DG functor carries identity closed degree-`0` morphisms to identities. -/
@[simp] theorem mapCompHom_id (F : DGFunctor) (X : A) :
    mapCompHom F (CompHom.id X) = CompHom.id (F.obj X) := by
  ext
  exact F.map_id X

/-- A DG functor carries composition of closed degree-`0` morphisms to composition. -/
@[simp] theorem mapCompHom_comp (F : DGFunctor) {X Y Z : A}
    (f : CompHom X Y) (g : CompHom Y Z) :
    mapCompHom F (CompHom.comp f g) = CompHom.comp (mapCompHom F f) (mapCompHom F g) := by
  ext
  simpa [CompHom.comp_val] using F.map_comp g.val f.val

/-- Lemma 22.26.5 (1): a DG functor induces a functor `Comp(𝒜) ⥤ Comp(𝒝)`. -/
@[stacks 09L8]
def mapComp (F : DGFunctor) : Comp R A ⥤ Comp R B where
  obj X := ⟨F.obj X⟩
  map f := mapCompHom F f
  map_id X := mapCompHom_id F X.obj
  map_comp f g := mapCompHom_comp F f g

/-- The induced functor on `Comp(𝒜)` acts on objects by the underlying DG functor. -/
@[simp] theorem mapComp_obj (F : DGFunctor) (X : Comp R A) :
    (mapComp F).obj X = ⟨F.obj X⟩ := rfl

/-- The induced functor on `Comp(𝒜)` acts on morphisms by `mapCompHom`. -/
@[simp] theorem mapComp_map (F : DGFunctor) {X Y : Comp R A} (f : X ⟶ Y) :
    (mapComp F).map f = mapCompHom F f := rfl

/-- A DG functor preserves the homotopy relation on closed degree-`0` morphisms. -/
theorem map_homotopy {F : DGFunctor} {X Y : A} {f g : CompHom X Y}
    (hfg : Homotopic X Y f g) :
    Homotopic (F.obj X) (F.obj Y) (mapCompHom F f) (mapCompHom F g) := by
  rcases hfg with ⟨hfg', hhfg⟩
  refine ⟨F.map hfg', ?_⟩
  calc
    (mapCompHom F f).val - (mapCompHom F g).val = F.map (f.val - g.val) := by
      simp [mapCompHom, F.map_sub]
    _ = F.map (DA.d (-1) hfg') := by
      simpa [hhfg]
    _ = DB.d (-1) (F.map hfg') := by
      simpa using (F.map_d hfg')

/-- Lemma 22.26.5 (2): a DG functor induces a functor `K(𝒜) ⥤ K(𝒝)`. -/
@[stacks 09L8]
def mapK (F : DGFunctor) : K R A ⥤ K R B where
  obj X := ⟨F.obj X⟩
  map := fun {X Y} (f : HomotopyClass (X : A) (Y : A)) ↦
    _root_.Quotient.map (fun g ↦ mapCompHom F g) (fun _ _ hfg ↦ map_homotopy hfg) f
  map_id X := by
    change (mapCompHom F (CompHom.id (X : A))).toHomotopyClass =
      (CompHom.id (F.obj X)).toHomotopyClass
    simpa using congrArg CompHom.toHomotopyClass (mapCompHom_id F (X : A))
  map_comp f g := by
    refine _root_.Quotient.inductionOn₂ f g ?_
    intro f g
    change (mapCompHom F (CompHom.comp f g)).toHomotopyClass =
      (CompHom.comp (mapCompHom F f) (mapCompHom F g)).toHomotopyClass
    simpa using congrArg CompHom.toHomotopyClass (mapCompHom_comp F f g)

/-- The induced functor on `K(𝒜)` acts on objects by the underlying DG functor. -/
@[simp] theorem mapK_obj (F : DGFunctor) (X : K R A) :
    (mapK F).obj X = ⟨F.obj X⟩ := rfl

/-- Helper for Lemma 22.26.5: `mapK` sends a represented homotopy class to the class of the
mapped closed morphism. -/
@[simp] theorem mapK_map_toHomotopyClass (F : DGFunctor) {X Y : A} (f : CompHom X Y) :
    (mapK F).map f.toHomotopyClass = (mapCompHom F f).toHomotopyClass := by
  -- This is immediate from the quotient-level definition of `mapK`.
  rfl

/-- Helper for Lemma 22.26.5: on a morphism of `Comp(𝒜)`, the induced functor `mapK` is
represented by the mapped closed degree-`0` morphism. -/
@[simp] theorem mapK_map_compHom (F : DGFunctor) {X Y : Comp R A} (f : X ⟶ Y) :
    (mapK F).map f.inK = (mapCompHom F f).toHomotopyClass := by
  -- Rewrite the `Comp` morphism as its represented homotopy class and use the representative API.
  simpa [CompHom.inK_eq_toHomotopyClass] using
    mapK_map_toHomotopyClass (F := F) (f := f)

/-- Helper for Lemma 22.26.5: the morphism induced by `mapComp` is represented in `K(𝒝)` by the
mapped closed degree-`0` morphism. -/
@[simp] theorem mapComp_map_toHomotopyClass (F : DGFunctor) {X Y : Comp R A} (f : X ⟶ Y) :
    ((mapComp F).map f).toHomotopyClass = (mapCompHom F f).toHomotopyClass := by
  -- Identify the `Comp`-level map with `mapCompHom` before passing to homotopy classes.
  simpa using congrArg CompHom.toHomotopyClass (mapComp_map (F := F) (f := f))

/-- Helper for Lemma 22.26.5: the morphism induced by `mapComp` is represented in `K(𝒝)` by the
mapped closed degree-`0` morphism. -/
@[simp] theorem mapComp_map_inK (F : DGFunctor) {X Y : Comp R A} (f : X ⟶ Y) :
    ((mapComp F).map f).inK = (mapCompHom F f).toHomotopyClass := by
  -- Normalize the `inK` morphism to the represented homotopy class and reuse the `Comp`-level API.
  simpa [CompHom.inK_eq_toHomotopyClass] using
    mapComp_map_toHomotopyClass (F := F) (f := f)

/-- Passing a closed degree-`0` morphism to `K(𝒜)` and then applying `mapK` agrees with first
applying `mapComp` and then passing to `K(𝒝)`. -/
@[simp] theorem mapK_map_inK (F : DGFunctor) {X Y : Comp R A} (f : X ⟶ Y) :
    (mapK F).map f.inK = ((mapComp F).map f).inK := by
  -- Route correction: finish at the representative level instead of reopening quotient reasoning.
  simpa using
    (mapK_map_compHom (F := F) (f := f)).trans (mapComp_map_inK (F := F) (f := f)).symm

end DgFunctor

end DifferentialGradedCategory
