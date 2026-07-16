import stacks_proof.stacks_project.Chap10.Lemma_10_102_2.Recoordinate
import stacks_proof.stacks_project.Chap10.Lemma_10_102_2.PivotNormalization

open CategoryTheory CategoryTheory.Limits ChainComplex Matrix

noncomputable section

universe u

section

variable {R : Type u} [Ring R]

namespace FiniteFreeComplex

variable {e : ℕ}
/-- Helper for Lemma 10.102.2: an equality of adjacent ranks identifies the corresponding
standard free modules. -/
theorem finArrow_eq_of_eq {m n : ℕ} (h : m = n) :
    (Fin m → R) = (Fin n → R) := by
  -- This is just the dependent rewrite on the finite indexing type.
  cases h
  rfl

/-- Helper for Lemma 10.102.2: transport the standard free module along an equality of ranks. -/
noncomputable def moduleIso_of_eq {m n : ℕ} (h : m = n) :
    ModuleCat.of R (Fin m → R) ≅ ModuleCat.of R (Fin n → R) :=
  match h with
  | rfl => Iso.refl _

/-- Helper for Lemma 10.102.2: transporting along a rank equality does not change evaluation at
the corresponding casted coordinate. -/
theorem moduleIso_of_eq_hom_apply_cast
    {m n : ℕ} (h : m = n) (x : Fin m → R) (b : Fin m) :
    ((moduleIso_of_eq (R := R) h).hom.hom x) (cast (congrArg Fin h) b) = x b := by
  cases h
  rfl

/-- Helper for Lemma 10.102.2: transporting the pure basis vector along a rank equality and then
pulling it back by the inverse transport recovers the original basis vector. -/
theorem moduleIso_of_eq_inv_apply_single_cast
    {m n : ℕ} (h : m = n) (a : Fin m) :
    (moduleIso_of_eq (R := R) h).inv.hom (Pi.single (cast (congrArg Fin h) a) (1 : R)) =
      (Pi.single a (1 : R) : Fin m → R) := by
  cases h
  rfl

/-- Helper for Lemma 10.102.2: transport the middle differential to explicit successor-coordinate
modules once the adjacent ranks have been written as `ns + 1` and `nt + 1`. -/
noncomputable def diffAt_transport_to_successor_ranks
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    {ns nt : ℕ}
    (hsucc : C.rank i.succ = ns + 1)
    (hcast : C.rank i.castSucc = nt + 1) :
    (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R) :=
  let sourceEq := moduleIso_of_eq (R := R) hsucc
  let targetEq := moduleIso_of_eq (R := R) hcast
  (sourceEq.inv ≫ ModuleCat.ofHom (C.diffAt i) ≫ targetEq.hom).hom

/-- Helper for Lemma 10.102.2: the transported middle differential is exactly the original middle
map conjugated by the rank-transport isomorphisms. -/
@[simp] theorem diffAt_transport_to_successor_ranks_hom
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    {ns nt : ℕ}
    (hsucc : C.rank i.succ = ns + 1)
    (hcast : C.rank i.castSucc = nt + 1) :
    ModuleCat.ofHom (diffAt_transport_to_successor_ranks (R := R) (C := C) (i := i) hsucc hcast) =
      (moduleIso_of_eq (R := R) hsucc).inv ≫ ModuleCat.ofHom (C.diffAt i) ≫
        (moduleIso_of_eq (R := R) hcast).hom := by
  -- The transport definition was chosen precisely so that its `ModuleCat` morphism is this
  -- conjugated composite.
  rfl

/-- Helper for Lemma 10.102.2: evaluating the transported middle differential on the transported
pivot basis vector is exactly the original matrix coefficient. -/
theorem diffAt_transport_to_successor_ranks_entry
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    {ns nt : ℕ}
    (hsucc : C.rank i.succ = ns + 1)
    (hcast : C.rank i.castSucc = nt + 1)
    (a : Fin (C.rank i.succ))
    (b : Fin (C.rank i.castSucc)) :
    let a' : Fin (ns + 1) := cast (congrArg Fin hsucc) a
    let b' : Fin (nt + 1) := cast (congrArg Fin hcast) b
    ((diffAt_transport_to_successor_ranks (R := R) (C := C) (i := i) hsucc hcast)
      (Pi.single a' (1 : R))) b' = C.diffEntry i a b := by
  -- Expand the transported map and rewrite the source and target transports by the two cast
  -- compatibility lemmas.
  change
    ((moduleIso_of_eq (R := R) hcast).hom.hom
        (C.diffAt i
          (((moduleIso_of_eq (R := R) hsucc).inv.hom)
            (Pi.single (cast (congrArg Fin hsucc) a) (1 : R)))))
      (cast (congrArg Fin hcast) b) =
    C.diffEntry i a b
  rw [moduleIso_of_eq_inv_apply_single_cast (R := R) hsucc a,
    moduleIso_of_eq_hom_apply_cast (R := R) hcast (C.diffAt i (Pi.single a (1 : R))) b]
  rfl

/-- Helper for Lemma 10.102.2: transporting the chosen pivot coordinates to the explicit
successor-coordinate modules preserves the unit-entry witness. -/
theorem diffAt_transport_to_successor_ranks_pivot
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    {ns nt : ℕ}
    (hsucc : C.rank i.succ = ns + 1)
    (hcast : C.rank i.castSucc = nt + 1)
    (a : Fin (C.rank i.succ))
    (b : Fin (C.rank i.castSucc))
    (hu : IsUnit (C.diffEntry i a b)) :
    let a' : Fin (ns + 1) := cast (congrArg Fin hsucc) a
    let b' : Fin (nt + 1) := cast (congrArg Fin hcast) b
    IsUnit
      ((diffAt_transport_to_successor_ranks (R := R) (C := C) (i := i) hsucc hcast)
        (Pi.single a' (1 : R)) b') := by
  -- Route correction: reduce the transported pivot entry to the original coefficient by the exact
  -- transported-entry formula, then reuse the given unit witness.
  dsimp
  rw [diffAt_transport_to_successor_ranks_entry (R := R) (C := C) (i := i) hsucc hcast a b]
  exact hu

/-- Helper for Lemma 10.102.2: the head-tail splitting can be transported across a rank equality
without changing its mathematical content. -/
noncomputable def splitOffUnitModuleIso_of_eq
    {n ns : ℕ} (h : n = ns + 1) :
    ModuleCat.of R (Fin n → R) ≅
      biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)) :=
  moduleIso_of_eq (R := R) h ≪≫ splitOffUnitModuleIso (R := R) ns

/-- Helper for Lemma 10.102.2: after transporting to explicit successor-coordinate modules, the
adjacent-degree recoordination cancels the outer rank transports and leaves only the explicit
normalized basis changes. -/
theorem recoordinate_middle_diff_transport_cancel
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    {ns nt : ℕ}
    (hsucc : C.rank i.succ = ns + 1)
    (hcast : C.rank i.castSucc = nt + 1)
    (uSuccExp :
      ModuleCat.of R (Fin (ns + 1) → R) ≅
        ModuleCat.of R (Fin (ns + 1) → R))
    (uTargetExp :
      ModuleCat.of R (Fin (nt + 1) → R) ≅
        ModuleCat.of R (Fin (nt + 1) → R)) :
    let sourceEq := moduleIso_of_eq (R := R) hsucc
    let targetEq := moduleIso_of_eq (R := R) hcast
    let f := diffAt_transport_to_successor_ranks (R := R) (C := C) (i := i) hsucc hcast
    let uSucc := sourceEq ≪≫ uSuccExp ≪≫ sourceEq.symm
    let uTarget := targetEq ≪≫ uTargetExp ≪≫ targetEq.symm
    let D := recoordinateAtAdjacentDegrees C i uSucc uTarget
    sourceEq.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ targetEq.hom =
      uSuccExp.inv ≫ ModuleCat.ofHom f ≫ uTargetExp.hom := by
  -- Rewrite the recoordinated middle differential in adjacent-degree coordinates and cancel the
  -- two outer transports coming from `sourceEq` and `targetEq`.
  let sourceEq := moduleIso_of_eq (R := R) hsucc
  let targetEq := moduleIso_of_eq (R := R) hcast
  let f := diffAt_transport_to_successor_ranks (R := R) (C := C) (i := i) hsucc hcast
  let uSucc := sourceEq ≪≫ uSuccExp ≪≫ sourceEq.symm
  let uTarget := targetEq ≪≫ uTargetExp ≪≫ targetEq.symm
  let D := recoordinateAtAdjacentDegrees C i uSucc uTarget
  change sourceEq.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ targetEq.hom =
      uSuccExp.inv ≫ ModuleCat.ofHom f ≫ uTargetExp.hom
  have hD :
      ModuleCat.ofHom (D.diffAt i) =
        uSucc.inv ≫ ModuleCat.ofHom (C.diffAt i) ≫ uTarget.hom := by
    simpa [D] using
      recoordinateAtAdjacentDegrees_diffAt (R := R) (C := C) (i := i) (uSucc := uSucc)
        (uCast := uTarget)
  calc
    sourceEq.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ targetEq.hom =
        sourceEq.inv ≫ (uSucc.inv ≫ ModuleCat.ofHom (C.diffAt i) ≫ uTarget.hom) ≫ targetEq.hom := by
          simpa [Category.assoc] using
            congrArg (fun m ↦ sourceEq.inv ≫ m ≫ targetEq.hom) hD
    _ =
        uSuccExp.inv ≫
          ((moduleIso_of_eq (R := R) hsucc).inv ≫ ModuleCat.ofHom (C.diffAt i) ≫
            (moduleIso_of_eq (R := R) hcast).hom) ≫
          uTargetExp.hom := by
          simp [sourceEq, targetEq, uSucc, uTarget, Category.assoc]
    _ = uSuccExp.inv ≫ ModuleCat.ofHom f ≫ uTargetExp.hom := by
          rw [diffAt_transport_to_successor_ranks_hom (R := R) (C := C) (i := i) hsucc hcast]


end FiniteFreeComplex

end
