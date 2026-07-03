import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_3_1 (from Chap01) -/
universe u

variable {X : Type u} [TopologicalSpace X] {x y : X}

open FundamentalGroup
open Path.Homotopic.Quotient
open scoped FundamentalGroup

/- Definition 1.3.1: for a path `a : Path x y`, the basepoint-change map
`γ[a] : π₁(X, x) → π₁(X, y)` is the canonical equivalence
`FundamentalGroup.fundamentalGroupMulEquivOfPath a`, acting by conjugation with `a`. -/
recall FundamentalGroup.fundamentalGroupMulEquivOfPath (a : Path x y) :
    FundamentalGroup X x ≃* FundamentalGroup X y

scoped[FundamentalGroup] notation "γ[" a "]" => fundamentalGroupMulEquivOfPath a

/-- The canonical basepoint-change equivalence sends a loop class to its conjugate by the given
path. -/
theorem fundamentalGroupMulEquivOfPath_apply_fromPath (a : Path x y) (f : Path x x) :
    γ[a] (fromPath ⟦f⟧) = fromPath ⟦(a.symm.trans f).trans a⟧ := by
  change mk (a.symm.trans (f.trans a)) = mk ((a.symm.trans f).trans a)
  rw [eq]
  exact (Path.Homotopic.trans_assoc a.symm f a).symm

/-! ### Lemma_1_3_2 (from Chap01) -/
universe u

variable {X : Type u} [TopologicalSpace X] {x y : X}

open CategoryTheory FundamentalGroup
open Path.Homotopic.Quotient
open scoped FundamentalGroup

/-- Lemma 1.3.2 (1): the basepoint-change equivalence associated to a path `a : Path x y`
depends only on the endpoint-fixed homotopy class of `a`. -/
-- Proof sketch: identify `FundamentalGroup.fundamentalGroupMulEquivOfPath a` with conjugation by
-- the image of `a` in the fundamental groupoid, then use that homotopic paths define the same
-- morphism in the quotient groupoid.
lemma fundamentalGroupMulEquivOfPath_homotopic_eq {a b : Path x y} (h : a.Homotopic b) :
    γ[a] = γ[b] := by
  simpa [fundamentalGroupMulEquivOfPath] using
    congrArg (fun q ↦ ((Groupoid.isoEquivHom ..).symm q).conj) (eq.2 h)

/-- Lemma 1.3.2 (2): for a path `a : Path x y`, the basepoint-change map `γ[a]` preserves
multiplication on fundamental groups. -/
theorem fundamentalGroupMulEquivOfPath_map_mul
    (a : Path x y) (g h : FundamentalGroup X x) :
    γ[a] (g * h) = γ[a] g * γ[a] h := by
  exact (γ[a]).map_mul g h

/-! ### Lemma_1_3_3 (from Chap01) -/
universe u

variable {X : Type u} [TopologicalSpace X] {x y z : X}

open CategoryTheory
open scoped FundamentalGroup

/-- Lemma 1.3.3: basepoint change along a composite path is the composite of the corresponding
basepoint-change equivalences, so `γ[b · a] = γ[b] ∘ γ[a]`. -/
-- Proof sketch: view `FundamentalGroup.fundamentalGroupMulEquivOfPath` as conjugation by the
-- corresponding morphism in the fundamental groupoid, identify the class of `a.trans b` with the
-- composite of the classes of `a` and `b`, and use functoriality of conjugation under
-- composition.
theorem fundamentalGroupMulEquivOfPath_trans (a : Path x y) (b : Path y z) :
    γ[a.trans b] = (γ[a]).trans (γ[b]) := by
  let α : FundamentalGroupoid.mk x ≅ FundamentalGroupoid.mk y :=
    (Groupoid.isoEquivHom _ _).symm ⟦a⟧
  let β : FundamentalGroupoid.mk y ≅ FundamentalGroupoid.mk z :=
    (Groupoid.isoEquivHom _ _).symm ⟦b⟧
  have hcomp : (Groupoid.isoEquivHom _ _).symm ⟦a.trans b⟧ = α ≪≫ β := by
    ext
    rfl
  ext f
  rw [FundamentalGroup.fundamentalGroupMulEquivOfPath, hcomp]
  change (α ≪≫ β).conj f = β.conj (α.conj f)
  exact Iso.trans_conj α β f

/-! ### Proposition_1_3_4 (from Chap01) -/
universe u

variable {X : Type u} [TopologicalSpace X] {x y : X}

open CategoryTheory
open scoped FundamentalGroup

/-- Helper for Proposition 1.3.4: the isomorphism in the fundamental groupoid represented by the
reversed path is the inverse of the isomorphism represented by the original path. -/
lemma path_symm_iso_eq_inverse (a : Path x y) :
    ((Groupoid.isoEquivHom
      (FundamentalGroupoid.mk x)
      (FundamentalGroupoid.mk y)).symm ⟦a⟧).symm =
      (Groupoid.isoEquivHom
        (FundamentalGroupoid.mk y)
        (FundamentalGroupoid.mk x)).symm ⟦a.symm⟧ := by
  -- The quotient representatives are definitionally inverse after reversing the path.
  ext
  rfl

/-- Proposition 1.3.4: the inverse of the basepoint-change equivalence associated to a path
`a : Path x y` is the basepoint-change equivalence associated to the reversed path `a.symm`. -/
-- Proof sketch: `γ[a]` is conjugation by the isomorphism in the fundamental groupoid represented
-- by `a`. The inverse of that conjugation is conjugation by the inverse isomorphism, and the
-- inverse isomorphism is represented by the reversed path `a.symm`.
theorem fundamentalGroupMulEquivOfPath_symm (a : Path x y) :
    (γ[a]).symm = γ[a.symm] := by
  -- Replace conjugation by the inverse isomorphism with conjugation by the reversed path.
  simpa [FundamentalGroup.fundamentalGroupMulEquivOfPath] using
    congrArg Iso.conj (path_symm_iso_eq_inverse a)

/-! ### Lemma_1_3_5 (from Chap01) -/
universe u

variable {X : Type u} [TopologicalSpace X] {x y : X}

open CategoryTheory FundamentalGroup
open scoped FundamentalGroup

/-- Helper for Lemma 1.3.5: the path obtained by inserting the comparison loop
`a.trans b.symm` before `b` is homotopic to `a`. -/
lemma trans_symm_cancel_homotopic (a b : Path x y) :
    ((a.trans b.symm).trans b).Homotopic a := by
  -- Reassociate the concatenation so that `b.symm.trans b` cancels to the constant path.
  refine (Path.Homotopic.trans_assoc a b.symm b).trans ?_
  -- Replace the middle loop by the constant path and then remove the trailing constant segment.
  refine (Path.Homotopic.hcomp (Path.Homotopic.refl a) (Path.Homotopic.symm_trans b)).trans ?_
  exact Path.Homotopic.trans_refl a

/-- Helper for Lemma 1.3.5: conjugation by a loop class fixes every element of an Abelian
fundamental group. -/
lemma groupoid_conj_eq_self_of_commutative
    [Std.Commutative ((· * ·) : FundamentalGroup X x → FundamentalGroup X x → FundamentalGroup X x)]
    (α : FundamentalGroupoid.mk x ≅ FundamentalGroupoid.mk x) (g : FundamentalGroup X x) :
    α.conj g = g := by
  -- Convert commutativity in `π₁(X, x)` into commutation of the corresponding endomorphisms.
  rw [Iso.conj_apply]
  have hmul :
      (FundamentalGroup.fromArrow α.hom : FundamentalGroup X x) * g =
        g * (FundamentalGroup.fromArrow α.hom : FundamentalGroup X x) :=
    Std.Commutative.comm _ _
  have hcomm :
      g ≫ α.hom = α.hom ≫ g := by
    simpa [CategoryTheory.End.mul_def] using
      hmul
  -- Once the middle terms commute, the inverse and forward path cancel.
  calc
    α.inv ≫ g ≫ α.hom = α.inv ≫ (α.hom ≫ g) := by
      rw [hcomm]
    _ = (α.inv ≫ α.hom) ≫ g := by
      rw [← Category.assoc]
    _ = g := by
      simp

/-- Helper for Lemma 1.3.5: basepoint change along a loop at `x` is the identity when
`π₁(X, x)` is Abelian. -/
lemma fundamentalGroupMulEquivOfLoop_eq_one_of_commutative
    [Std.Commutative ((· * ·) : FundamentalGroup X x → FundamentalGroup X x → FundamentalGroup X x)]
    (ℓ : Path x x) :
    γ[ℓ] = (1 : FundamentalGroup X x ≃* FundamentalGroup X x) := by
  let α : FundamentalGroupoid.mk x ≅ FundamentalGroupoid.mk x :=
    (Groupoid.isoEquivHom _ _).symm ⟦ℓ⟧
  -- Unfold the loop action to conjugation by the corresponding groupoid isomorphism.
  ext g
  change α.conj g = g
  exact groupoid_conj_eq_self_of_commutative α g

/-- Lemma 1.3.5: if the fundamental group `π₁(X, x)` is Abelian, then the basepoint-change
isomorphism `γ[a] : π₁(X, x) → π₁(X, y)` is independent of the chosen path class from `x` to
`y`. -/
-- Proof sketch: compare `a` and `b` through the loop `a.trans b.symm` at `x`, use
-- `fundamentalGroupMulEquivOfPath_homotopic_eq` and `fundamentalGroupMulEquivOfPath_trans` to
-- write `γ[a]` as the composite of `γ[b]` with the loop-induced automorphism, and then use
-- commutativity of the canonical multiplication on `FundamentalGroup X x` to show that
-- conjugation automorphism is the identity.
theorem fundamentalGroupMulEquivOfPath_eq_of_abelian
    [Std.Commutative ((· * ·) : FundamentalGroup X x → FundamentalGroup X x → FundamentalGroup X x)]
    (a b : Path x y) :
    γ[a] = γ[b] := by
  let loop := a.trans b.symm
  have hloop : γ[loop] = (1 : FundamentalGroup X x ≃* FundamentalGroup X x) :=
    fundamentalGroupMulEquivOfLoop_eq_one_of_commutative loop
  have hpath : (loop.trans b).Homotopic a :=
    trans_symm_cancel_homotopic a b
  -- Compare `a` with `b` through the loop `a.trans b.symm` based at `x`.
  calc
    γ[a] = γ[loop.trans b] := by
      simpa [loop] using (fundamentalGroupMulEquivOfPath_homotopic_eq hpath).symm
    -- Split basepoint change along the composite into the loop action followed by `γ[b]`.
    _ = (γ[loop]).trans (γ[b]) :=
      fundamentalGroupMulEquivOfPath_trans loop b
    -- The loop action is trivial in an Abelian fundamental group.
    _ = γ[b] := by
      rw [hloop]
      ext g
      rfl

/-! ### Remark_1_3_6 (from Chap01) -/
noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X] {x y : X}

open scoped FundamentalGroup

/-- Remark 1.3.6: when `π₁(X, x)` is Abelian, all basepoints in the same path component are
canonically identified at the level of the fundamental group, since the basepoint-change
equivalence attached to `Joined x y` agrees with the one induced by any path from `x` to `y`. -/
-- Proof sketch: apply Lemma 1.3.5 to the two paths `h.somePath` and `a`, using commutativity of
-- `FundamentalGroup X x` to conclude that their induced basepoint-change equivalences coincide.
theorem fundamentalGroupMulEquivOfJoined_eq_of_path
    [Std.Commutative ((· * ·) : FundamentalGroup X x → FundamentalGroup X x → FundamentalGroup X x)]
    (h : Joined x y) (a : Path x y) :
    γ[h.somePath] = γ[a] :=
  fundamentalGroupMulEquivOfPath_eq_of_abelian h.somePath a
