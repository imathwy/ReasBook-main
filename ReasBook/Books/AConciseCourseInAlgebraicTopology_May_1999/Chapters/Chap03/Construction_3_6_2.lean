module

public import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.GroupoidStarAction

public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open CategoryTheory.Groupoid (homMulAction_smul)

variable {B : Type u} [Groupoid.{v} B]

/-- The restricted `H`-action on `b ⟶ x` is still given by precomposition with inverse loops. -/
@[simp] theorem orbitCoveringFiber_subgroup_smul (b x : B) (H : Subgroup (End b))
    (h : H) (f : b ⟶ x) :
    h • f = inv (h : End b) ≫ f := by
  change ((h : End b) • f) = inv (h : End b) ≫ f
  simp [homMulAction_smul]

/-- Construction 3.6.2: the objects of the covering attached to `H ≤ π(B,b)` are the right
`H`-cosets of arrows in the star of `b`; over a fixed target `x : B`, the corresponding fiber is
the quotient of `b ⟶ x` by the precomposition action of `H`. -/
abbrev orbitCoveringFiber (b : B) (H : Subgroup (End b)) (x : B) :=
  MulAction.orbitRel.Quotient H (b ⟶ x)

/-- Two arrows with source `b` represent the same point of the fiber over `x` exactly when they
differ by precomposition with an element of `H`. -/
@[simp] theorem orbitCoveringFiber_mk_eq_mk_iff (b : B) (H : Subgroup (End b)) {x : B}
    (f f' : b ⟶ x) :
    (Quotient.mk'' f : orbitCoveringFiber b H x) = Quotient.mk'' f' ↔
      ∃ h : H, inv (h : End b) ≫ f' = f := by
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  simp [orbitCoveringFiber_subgroup_smul]

/-- Construction 3.6.2: the objects of the covering attached to `H ≤ π(B,b)` form the sigma type
of base objects together with a coset in the corresponding fiber. -/
abbrev orbitCoveringObj (b : B) (H : Subgroup (End b)) : Type (max u v) :=
  Σ x : B, orbitCoveringFiber b H x

/-- The object of the covering represented by the right coset of an arrow `f : b ⟶ x`. -/
noncomputable abbrev orbitCoveringObjOfHom (b : B) (H : Subgroup (End b)) {x : B} (f : b ⟶ x) :
    orbitCoveringObj b H :=
  ⟨x, Quotient.mk'' f⟩

/-- The canonical base-groupoid projection of the coset represented by `f` is the target of `f`. -/
@[simp] theorem orbitCoveringObjOfHom_fst (b : B) (H : Subgroup (End b))
    {x : B} (f : b ⟶ x) :
    Sigma.fst (orbitCoveringObjOfHom b H f) = x := rfl

/-- The fiber component of the covering object represented by `f` is the orbit class of `f`. -/
@[simp] theorem orbitCoveringObjOfHom_snd (b : B) (H : Subgroup (End b))
    {x : B} (f : b ⟶ x) :
    Sigma.snd (orbitCoveringObjOfHom b H f) = Quotient.mk'' f :=
  rfl

/-- Two arrows with common target `x` represent the same covering object exactly when they differ
by precomposition with an element of `H`. -/
@[simp] theorem orbitCoveringObjOfHom_eq_iff (b : B) (H : Subgroup (End b))
    {x : B} (f f' : b ⟶ x) :
    orbitCoveringObjOfHom b H f = orbitCoveringObjOfHom b H f' ↔
      ∃ h : H, inv (h : End b) ≫ f' = f := by
  simp [orbitCoveringObjOfHom, orbitCoveringFiber_mk_eq_mk_iff]

end
