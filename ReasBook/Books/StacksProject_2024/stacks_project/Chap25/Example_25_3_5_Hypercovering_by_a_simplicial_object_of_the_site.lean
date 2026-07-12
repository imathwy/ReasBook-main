import StacksProject_2024.Chap25.Lemma_25_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open SemiRepresentableFamily.Over
open scoped CategoryTheory.SemiRepresentableFamily
open scoped Simplicial

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasPullbacks C]
variable {X : C}

-- Semantic search note: no `lean_leansearch` tool was available in this run; the statement shape
-- follows the local Chapter 25 `Hypercovering` owner and the fixed-target `SR(C, X)` API, using
-- the direct Chapter 25 owners rather than the intermediate recall wrappers.

section

omit [HasPullbacks C]

/-- The singleton-family embedding of the slice category `C / X` into the fixed-target family
category `SR(C, X)`. -/
private def overToSingletonFamily (X : C) :
    CategoryTheory.Over X ⥤ SemiRepresentableFamily.Over.{v, u, max u v} X where
  obj Y :=
    ofArrows
      (fun _ : PUnit ↦ Y.left)
      (fun _ ↦ Y.hom)
  map φ :=
    ⟨fun _ ↦ PUnit.unit, fun _ ↦ φ⟩
  map_id := by
    sorry
  map_comp := by
    sorry

/-- The augmented simplicial object `a : U ⟶ X` viewed in the slice category `C / X`. -/
private def siteAugmentedSimplicialObjectOver
    (U : SimplicialObject C)
    (a : U ⟶ (SimplicialObject.const C).obj X) :
    SimplicialObject (CategoryTheory.Over X) where
  obj Δ := Over.mk (a.app Δ)
  map f := Over.homMk (U.map f) (by simpa using a.naturality f)
  map_id := by
    sorry
  map_comp := by
    sorry

/-- The simplicial object of `SR(C, X)` obtained by viewing each degree of an augmented simplicial
object as the singleton family over `X` with that augmentation component. This is the source-facing
singleton-family view of the canonical simplicial object in `C / X`. -/
def siteAugmentedSimplicialObject
    (U : SimplicialObject C)
    (a : U ⟶ (SimplicialObject.const C).obj X) :
    SimplicialObject (SemiRepresentableFamily.Over.{v, u, max u v} X) :=
  siteAugmentedSimplicialObjectOver U a ⋙ overToSingletonFamily X

/-- Each degree of `siteAugmentedSimplicialObject U a` is the singleton family on `U.obj Δ`. -/
@[simp] theorem siteAugmentedSimplicialObject_obj_left
    (U : SimplicialObject C)
    (a : U ⟶ (SimplicialObject.const C).obj X)
    (Δ : SimplexCategoryᵒᵖ)
    (i : PUnit) :
    (((siteAugmentedSimplicialObject U a).obj Δ).obj i).left = U.obj Δ := by
  cases i
  rfl

/-- The structure map of the unique component of `(siteAugmentedSimplicialObject U a).obj Δ` is
the augmentation component `a.app Δ`. -/
@[simp] theorem siteAugmentedSimplicialObject_obj_hom
    (U : SimplicialObject C)
    (a : U ⟶ (SimplicialObject.const C).obj X)
    (Δ : SimplexCategoryᵒᵖ)
    (i : PUnit) :
    (((siteAugmentedSimplicialObject U a).obj Δ).obj i).hom = a.app Δ := by
  cases i
  rfl

/-- The index map of each simplicial structure morphism of `siteAugmentedSimplicialObject U a` is
the unique map on `PUnit`. -/
@[simp] theorem siteAugmentedSimplicialObject_map_f
    {Δ Δ' : SimplexCategoryᵒᵖ}
    (U : SimplicialObject C)
    (a : U ⟶ (SimplicialObject.const C).obj X)
    (f : Δ ⟶ Δ') :
    ((siteAugmentedSimplicialObject U a).map f).f = fun _ ↦ PUnit.unit :=
  rfl

/-- The unique component of the simplicial structure morphism of `siteAugmentedSimplicialObject U
a` is induced by `U.map f` and the augmentation naturality square. -/
@[simp] theorem siteAugmentedSimplicialObject_map_φ
    {Δ Δ' : SimplexCategoryᵒᵖ}
    (U : SimplicialObject C)
    (a : U ⟶ (SimplicialObject.const C).obj X)
    (f : Δ ⟶ Δ')
    (i : PUnit) :
    ((siteAugmentedSimplicialObject U a).map f).φ i =
      Over.homMk (U.map f) (by simpa using a.naturality f) := by
  cases i
  rfl

end

/-- The degree-`1` comparison map `U₁ ⟶ U₀ ×_X U₀` induced by the augmentation. -/
noncomputable def siteAugmentedSimplicialObjectOneMap
    (U : SimplicialObject C)
    (a : U ⟶ (SimplicialObject.const C).obj X) :
    U.obj (op ⦋1⦌) ⟶
      pullback
        (a.app (op ⦋0⦌))
        (a.app (op ⦋0⦌)) :=
  pullback.lift
    (U.δ 0)
    (U.δ 1)
    (by
      have h₀ := a.naturality (SimplexCategory.δ (0 : Fin 2)).op
      have h₁ := a.naturality (SimplexCategory.δ (1 : Fin 2)).op
      simpa using h₀.trans h₁.symm)

/-- The higher comparison map `U_{n + 1} ⟶ (cosk_n sk_n U)_{n + 1}`. -/
abbrev siteAugmentedSimplicialObjectHigherMap
    (U : SimplicialObject C)
    (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    U.obj (op ⦋n + 1⦌) ⟶
      ((SimplicialObject.cosk n).obj U).obj
        (op ⦋n + 1⦌) :=
  ((SimplicialObject.coskAdj n).unit.app U).app
    (op ⦋n + 1⦌)

/-- The degree-`0` singleton family over `X` attached to the augmentation `U₀ ⟶ X`. -/
abbrev siteAugmentedSimplicialObjectZeroFamily
    (U : SimplicialObject C)
    (a : U ⟶ (SimplicialObject.const C).obj X) :
    SemiRepresentableFamily.Over.{v, u, max u v} X :=
  ofArrows
    (fun _ : PUnit ↦ U.obj (op ⦋0⦌))
    (fun _ ↦ a.app (op ⦋0⦌))

/-- The degree-`0` object of `siteAugmentedSimplicialObject U a` is the source-facing singleton
family `{U₀ ⟶ X}`. -/
@[simp] theorem siteAugmentedSimplicialObject_zero_obj
    (U : SimplicialObject C)
    (a : U ⟶ (SimplicialObject.const C).obj X) :
    (siteAugmentedSimplicialObject U a).obj (op ⦋0⦌) =
      siteAugmentedSimplicialObjectZeroFamily U a :=
  rfl

/-- The degree-`1` singleton family over `U₀ ×_X U₀` induced by the two face maps. -/
abbrev siteAugmentedSimplicialObjectOneFamily
    (U : SimplicialObject C)
    (a : U ⟶ (SimplicialObject.const C).obj X) :
    SemiRepresentableFamily.Over.{v, u, max u v}
      (pullback (a.app (op ⦋0⦌)) (a.app (op ⦋0⦌))) :=
  ofArrows
    (fun _ : PUnit ↦ U.obj (op ⦋1⦌))
    (fun _ ↦ siteAugmentedSimplicialObjectOneMap U a)

/-- The degree-`n + 1` singleton family over `(\operatorname{cosk}_n \operatorname{sk}_n U)_{n +
1}` induced by the canonical comparison map. -/
abbrev siteAugmentedSimplicialObjectHigherFamily
    (U : SimplicialObject C)
    (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    SemiRepresentableFamily.Over.{v, u, max u v}
      (((SimplicialObject.cosk n).obj U).obj (op ⦋n + 1⦌)) :=
  ofArrows
    (fun _ : PUnit ↦ U.obj (op ⦋n + 1⦌))
    (fun _ ↦ siteAugmentedSimplicialObjectHigherMap U n)

namespace Hypercovering

section

variable (K : Hypercovering J X)
variable (U : SimplicialObject C)
variable (a : U ⟶ (SimplicialObject.const C).obj X)

/-- Example 25.3.5 (Hypercovering by a simplicial object of the site) (1): if the singleton-family
lift of an augmented simplicial object is a hypercovering of `X`, then the family
`\{U_0 \to X\}` is covering. -/
@[stacks 0GM9]
theorem zero_isCovering_of_siteAugmentedSimplicialObject
    (hK : K.toSimplicialObject = siteAugmentedSimplicialObject U a)
    :
    (siteAugmentedSimplicialObjectZeroFamily U a).toSieve ∈ J X := sorry

/-- Example 25.3.5 (Hypercovering by a simplicial object of the site) (2): if the singleton-family
lift of an augmented simplicial object is a hypercovering of `X`, then the family
`\{U_1 \to U_0 \times_X U_0\}` induced by the two face maps is covering. -/
@[stacks 0GM9]
theorem one_isCovering_of_siteAugmentedSimplicialObject
    (hK : K.toSimplicialObject = siteAugmentedSimplicialObject U a)
    :
    (siteAugmentedSimplicialObjectOneFamily U a).toSieve ∈
      J (pullback (a.app (op ⦋0⦌)) (a.app (op ⦋0⦌))) := sorry

/-- Example 25.3.5 (Hypercovering by a simplicial object of the site) (3): if the singleton-family
lift of an augmented simplicial object is a hypercovering of `X`, then for every `n ≥ 1` the
family `\{U_{n + 1} \to (\operatorname{cosk}_n \operatorname{sk}_n U)_{n + 1}\}` is covering. -/
@[stacks 0GM9]
theorem higher_isCovering_of_siteAugmentedSimplicialObject
    (hK : K.toSimplicialObject = siteAugmentedSimplicialObject U a)
    (n : ℕ) (hn : 1 ≤ n)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    (siteAugmentedSimplicialObjectHigherFamily U n).toSieve ∈
      J (((SimplicialObject.cosk n).obj U).obj (op ⦋n + 1⦌)) := sorry

end

end Hypercovering

section

variable (U : SimplicialObject C)
variable (a : U ⟶ (SimplicialObject.const C).obj X)
variable (h1 : (siteAugmentedSimplicialObjectOneFamily U a).toSieve ∈
  J (pullback (a.app (op ⦋0⦌)) (a.app (op ⦋0⦌))))
variable (hHigher : ∀ n : ℕ, 1 ≤ n →
  ∀ [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F],
    (siteAugmentedSimplicialObjectHigherFamily U n).toSieve ∈
      J (((SimplicialObject.cosk n).obj U).obj (op ⦋n + 1⦌)))

/-- The degreewise covering hypotheses from Example 25.3.5(4) give the canonical higher matching
map covering conditions for the singleton-family lift. -/
theorem siteAugmentedSimplicialObject_succ_isCovering
    (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤
        SemiRepresentableFamily.Over.{v, u, max u v} X,
        (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    Hom.IsCovering J (matchingMap (siteAugmentedSimplicialObject U a) n) := sorry

variable (h0 : (siteAugmentedSimplicialObjectZeroFamily U a).toSieve ∈ J X)

/-- Example 25.3.5 (Hypercovering by a simplicial object of the site) (4): if the families
`\{U_0 \to X\}`, `\{U_1 \to U_0 \times_X U_0\}`, and
`\{U_{n + 1} \to (\operatorname{cosk}_n \operatorname{sk}_n U)_{n + 1}\}` for `n \geq 1` are
covering, then the singleton-family lift of the augmented simplicial object satisfies the
hypercovering conditions of `X`. -/
@[stacks 0GM9]
noncomputable abbrev siteAugmentedHypercovering
    :
    Hypercovering J X :=
  Hypercovering.ofSimplicial
    (siteAugmentedSimplicialObject U a)
    h0
    (siteAugmentedSimplicialObject_succ_isCovering U a h1 hHigher)

/-- The hypercovering of Example 25.3.5(4) has the expected underlying singleton-family
simplicial object. -/
@[simp] theorem siteAugmentedHypercovering_toSimplicialObject
    :
    (siteAugmentedHypercovering U a h0 h1 hHigher).toSimplicialObject =
      siteAugmentedSimplicialObject U a := by
  simpa [siteAugmentedHypercovering] using
    Hypercovering.ofSimplicial_toSimplicialObject
      (siteAugmentedSimplicialObject U a)
      h0
      (siteAugmentedSimplicialObject_succ_isCovering U a h1 hHigher)

/-- The degree-`0` covering field of `siteAugmentedHypercovering` is the given covering
hypothesis on `U₀ ⟶ X`. -/
@[simp] theorem siteAugmentedHypercovering_zero_isCovering
    :
    (siteAugmentedHypercovering U a h0 h1 hHigher).zero_isCovering = h0 := by
  simpa [siteAugmentedHypercovering] using
    Hypercovering.ofSimplicial_zero_isCovering
      (siteAugmentedSimplicialObject U a)
      h0
      (siteAugmentedSimplicialObject_succ_isCovering U a h1 hHigher)

/-- The higher matching-map covering fields of `siteAugmentedHypercovering` are exactly the
canonical covering conditions obtained from the source-facing singleton-family hypotheses. -/
@[simp] theorem siteAugmentedHypercovering_succ_isCovering
    (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤
        SemiRepresentableFamily.Over.{v, u, max u v} X,
        (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    (siteAugmentedHypercovering U a h0 h1 hHigher).succ_isCovering n =
      siteAugmentedSimplicialObject_succ_isCovering U a h1 hHigher n := by
  simpa [siteAugmentedHypercovering] using
    Hypercovering.ofSimplicial_succ_isCovering
      (siteAugmentedSimplicialObject U a)
      h0
      (siteAugmentedSimplicialObject_succ_isCovering U a h1 hHigher)
      n

end

end CategoryTheory
