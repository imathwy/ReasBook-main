import Mathlib
import stacks_proof.stacks_project.Chap06.Lemma_6_31_8
import stacks_proof.stacks_project.Chap17.Definition_17_17_1
import stacks_proof.stacks_project.Chap17.Lemma_17_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleSheaf

/-- Helper for Lemma 17.17.6: the extension by zero of the structure sheaf from the open subspace
`U` back to `X`. -/
abbrev openSubsetStructureSheafLowerShriek
    {X : RingedSpace.{u}} (U : Opens X.carrier) : RingedSpace.Modules X :=
  (openSubsetModuleSheafExtensionByZero U (RingedSpace.ringCatSheaf X)).obj
    (SheafOfModules.unit
      ((TopCat.Sheaf.pullback RingCat (extensionByZeroOpenSubsetInclusion U)).obj
        (RingedSpace.ringCatSheaf X)))

/-- Helper for Lemma 17.17.6: `openSubsetStructureSheafLowerShriek U` is definitionally the
explicit Chapter 6 extension-by-zero construction applied to the unit module on the open
subspace. -/
theorem openSubsetStructureSheafLowerShriek_def
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    openSubsetStructureSheafLowerShriek (X := X) U =
      (openSubsetModuleSheafExtensionByZero U (RingedSpace.ringCatSheaf X)).obj
        (SheafOfModules.unit
          ((TopCat.Sheaf.pullback RingCat (extensionByZeroOpenSubsetInclusion U)).obj
            (RingedSpace.ringCatSheaf X))) := by
  -- Proof comment: this simply unfolds the chapter-local lower-shriek owner to the explicit
  -- extension-by-zero construction used by the Chapter 6 stalk formulas.
  rfl

/-- Helper for Lemma 17.17.6: an `S`-module is linearly equivalent to the regular `S`-module once
its restriction of scalars along a ring equivalence is linearly equivalent to the regular
`R`-module. -/
private noncomputable def linearEquivOfRestrictScalarsRegular
    {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (M : ModuleCat S)
    (h : ((ModuleCat.restrictScalars e.toRingHom).obj M : ModuleCat R) ≃ₗ[R] R) :
    M ≃ₗ[S] S where
  toFun m := e (h (show ((ModuleCat.restrictScalars e.toRingHom).obj M : ModuleCat R) from m))
  invFun s := h.symm (e.symm s)
  map_add' m n := by
    simpa using congrArg e
      (h.map_add
        (show ((ModuleCat.restrictScalars e.toRingHom).obj M : ModuleCat R) from m)
        (show ((ModuleCat.restrictScalars e.toRingHom).obj M : ModuleCat R) from n))
  map_smul' s m := by
    let M' : ModuleCat R := (ModuleCat.restrictScalars e.toRingHom).obj M
    let r : R := e.symm s
    have hs : (show M' from s • m) = r • (show M' from m : M') := by
      change s • m = (e r) • m
      simp [r]
    calc
      e (h (show M' from s • m)) = e (h (r • (show M' from m : M'))) := by
        rw [hs]
      _ = e (r * h (show M' from m : M')) := by
        simpa [smul_eq_mul] using congrArg e (h.map_smul r (show M' from m : M'))
      _ = s * e (h (show M' from m : M')) := by
        simp [r]
  left_inv m := by
    calc
      h.symm
          (e.symm
            (e
              (h
                (show ((ModuleCat.restrictScalars e.toRingHom).obj M : ModuleCat R) from m)))) =
          h.symm
            (h
              (show ((ModuleCat.restrictScalars e.toRingHom).obj M : ModuleCat R) from m)) := by
        simp
      _ = m := by
        exact h.left_inv
          (show ((ModuleCat.restrictScalars e.toRingHom).obj M : ModuleCat R) from m)
  right_inv s := by
    simpa using congrArg e (h.apply_symm_apply (e.symm s))

/- Domain-style sampling for Lemma 17.17.6:
- primary domain: extension by zero for sheaves of modules on a ringed space, specialized to the
  structure sheaf on an open subspace, together with flatness of the resulting `\mathcal O_X`-module;
- sampled owner declarations:
  `SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero`,
  `SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero_isFlat`,
  `ringSheaf`,
  `Sheaf.over`,
  `SheafOfModules.IsFlat`;
- best owner abstraction: the project owner for the lower-shriek structure module is
  `SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero`, whose localized structure
  sheaf is already expressed through the canonical restriction surface `X.sheaf.over U`; the
  ringed-space statement here should be only a thin specialization of that owner and its flatness
  theorem;
- primitive data: an open subset `U ⊆ X`;
- derived API: the source-facing ringed-space statement that `j![X.sheaf, U] = j_{U!}\mathcal O_U`
  is flat.

Source/core/bridge triage:
- `source-facing`: the ringed-space flatness statement for `j_{U!}\mathcal O_U`;
- `core/canonical`: `SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero` and
  `SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero_isFlat`;
- `bridge/view`: the specialization from the ringed-site owner `(X, X.sheaf)` to the ringed-space
  module category `X.Modules`.

This file should therefore delete the parallel owner `structureSheafLowerShriek` and keep only the
source-facing ringed-space specialization of the canonical project owner `j![X.sheaf, U]`.
-/

/-- Helper for Lemma 17.17.6: after transporting along the open-immersion stalk ring isomorphism,
the stalk of the chapter-local lower-shriek structure sheaf at an inside point identifies with the
stalk of the restricted structure sheaf. -/
theorem openSubsetStructureSheafLowerShriek_stalkIso
    {X : RingedSpace.{u}} (U : Opens X.carrier) (xU : U) :
    (ModuleCat.restrictScalars
      (((TopCat.Sheaf.stalkPullbackIso
          (extensionByZeroOpenSubsetInclusion U) (RingedSpace.ringCatSheaf X) xU).symm).hom.hom)).obj
      (RingedSpace.stalkModuleCat (openSubsetStructureSheafLowerShriek (X := X) U) xU.1) ≅
        RingedSpace.stalkModuleCat
          (SheafOfModules.unit (RingedSpace.ringCatSheaf (X.restrict U.isOpenEmbedding))) xU := by
  -- Proof comment: specialize the Chapter 6 inside-stalk formula to the unit sheaf and rewrite
  -- both module owners onto the chapter-local `RingedSpace.stalkModuleCat` surface.
  simpa [openSubsetStructureSheafLowerShriek_def, RingedSpace.stalkModuleCat] using
    (openSubspaceModuleSheafExtensionByZero_stalkIso (X := X) (U := U)
      (ℱ := SheafOfModules.unit
        ((TopCat.Sheaf.pullback RingCat (extensionByZeroOpenSubsetInclusion U)).obj
          (RingedSpace.ringCatSheaf X))) xU)

/-- Helper for Lemma 17.17.6: the stalk of the chapter-local lower-shriek structure sheaf is zero
outside the open subset `U`. -/
theorem openSubsetStructureSheafLowerShriek_stalkIsZero_of_not_mem
    {X : RingedSpace.{u}} (U : Opens X.carrier) {x : X} (hx : x ∉ (U : Set X.carrier)) :
    IsZero (RingedSpace.stalkModuleCat (openSubsetStructureSheafLowerShriek (X := X) U) x) := by
  -- Proof comment: unfold the chapter-local owner once and reuse the Chapter 6 zero-stalk theorem
  -- for extension by zero outside `U`.
  simpa [openSubsetStructureSheafLowerShriek_def, RingedSpace.stalkModuleCat] using
    (openSubspaceModuleSheafExtensionByZero_stalk_isZero_of_not_mem (X := X) (U := U)
      (ℱ := SheafOfModules.unit
        ((TopCat.Sheaf.pullback RingCat (extensionByZeroOpenSubsetInclusion U)).obj
          (RingedSpace.ringCatSheaf X))) (x := x) hx)

/-- Helper for Lemma 17.17.6: at a point of `U`, the stalk of `j_{U!}\mathcal O_U` is flat
because it is linearly equivalent to the regular stalk module. -/
theorem openSubsetStructureSheafExtensionByZeroFlatAtOfMem
    {X : RingedSpace.{u}} (U : Opens X.carrier) {x : X} (hx : x ∈ (U : Set X.carrier)) :
    (openSubsetStructureSheafLowerShriek (X := X) U).flat_at x := by
  let xU : U := ⟨x, hx⟩
  let eRing :
      ((RingedSpace.ringCatSheaf (X.restrict U.isOpenEmbedding)).presheaf.stalk xU) ≃+*
        (X.presheaf.stalk x) :=
    ((TopCat.Sheaf.stalkPullbackIso
      (extensionByZeroOpenSubsetInclusion U) (RingedSpace.ringCatSheaf X) xU).symm).toRingEquiv
  have hRegular :
      ((ModuleCat.restrictScalars eRing.toRingHom).obj
        (RingedSpace.stalkModuleCat (openSubsetStructureSheafLowerShriek (X := X) U) x)) ≃ₗ[
          ((RingedSpace.ringCatSheaf (X.restrict U.isOpenEmbedding)).presheaf.stalk xU)]
        ((RingedSpace.ringCatSheaf (X.restrict U.isOpenEmbedding)).presheaf.stalk xU) := by
    -- Proof comment: first identify the ambient stalk with the restricted structure-sheaf stalk,
    -- then use the canonical linear equivalence for the unit sheaf on the restricted ringed space.
    exact
      (openSubsetStructureSheafLowerShriek_stalkIso (X := X) U xU).toLinearEquiv.trans
        (RingedSpace.unitStalkLinearEquiv (X := X.restrict U.isOpenEmbedding) xU)
  have hAmbient :
      RingedSpace.stalkModuleCat (openSubsetStructureSheafLowerShriek (X := X) U) x ≃ₗ[X.presheaf.stalk x]
        X.presheaf.stalk x :=
    linearEquivOfRestrictScalarsRegular eRing
      (RingedSpace.stalkModuleCat (openSubsetStructureSheafLowerShriek (X := X) U) x) hRegular
  -- Proof comment: a module linearly equivalent to the regular module is flat.
  simpa [SheafOfModules.flat_at] using Module.Flat.of_linearEquiv hAmbient

/-- Helper for Lemma 17.17.6: at a point outside `U`, the stalk of `j_{U!}\mathcal O_U` is zero,
hence free and therefore flat. -/
theorem openSubsetStructureSheafExtensionByZeroFlatAtOfNotMem
    {X : RingedSpace.{u}} (U : Opens X.carrier) {x : X} (hx : x ∉ (U : Set X.carrier)) :
    (openSubsetStructureSheafLowerShriek (X := X) U).flat_at x := by
  have hzero :
      IsZero (RingedSpace.stalkModuleCat (openSubsetStructureSheafLowerShriek (X := X) U) x) :=
    openSubsetStructureSheafLowerShriek_stalkIsZero_of_not_mem (X := X) U hx
  let _ : Subsingleton ↑(RingedSpace.stalkModuleCat (openSubsetStructureSheafLowerShriek (X := X) U) x) :=
    (ModuleCat.isZero_iff_subsingleton.1 hzero)
  let _ :
      Module.Free (X.presheaf.stalk x)
        ↑(RingedSpace.stalkModuleCat (openSubsetStructureSheafLowerShriek (X := X) U) x) :=
    Module.Free.of_subsingleton (R := X.presheaf.stalk x)
      (N := ↑(RingedSpace.stalkModuleCat (openSubsetStructureSheafLowerShriek (X := X) U) x))
  -- Proof comment: the zero stalk is subsingleton, hence free, so flatness follows immediately.
  simpa [SheafOfModules.flat_at] using
    (Module.Flat.of_free (R := X.presheaf.stalk x)
      (M := ↑(RingedSpace.stalkModuleCat (openSubsetStructureSheafLowerShriek (X := X) U) x)))

-- Proof sketch: by Lemma 17.17.2 it is enough to check flatness stalkwise. If `x ∈ U`, the stalk
-- of `j_{U!}\mathcal O_U` identifies with `\mathcal O_{U,x} \cong \mathcal O_{X,x}` by the
-- extension-by-zero stalk description on `U`, hence is flat over `\mathcal O_{X,x}`. If
-- `x ∉ U`, the stalk is zero by the extension-by-zero stalk description outside `U`, and the zero
-- module is flat.
/-- Lemma 17.17.6: for an open subset `U ⊆ X`, the extension by zero `j_{U!}\mathcal O_U`,
written here as `openSubsetStructureSheafLowerShriek U`, is a flat sheaf of `\mathcal O_X`-modules. -/
@[stacks 05NH]
theorem openSubsetStructureSheafExtensionByZero_isFlat
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    (openSubsetStructureSheafLowerShriek (X := X) U).IsFlat := by
  -- Route correction: instead of depending on the later Chapter 18 flatness owner, we execute the
  -- textbook stalkwise proof directly from the earlier Chapter 6 stalk descriptions.
  refine SheafOfModules.isFlat_of_stalkwise
    (openSubsetStructureSheafLowerShriek (X := X) U) ?_
  intro x
  -- Proof comment: the stalkwise proof is the textbook case split on whether the point lies in
  -- the open subset from which we extend by zero.
  by_cases hx : x ∈ (U : Set X.carrier)
  · simpa [SheafOfModules.flat_at] using
      (openSubsetStructureSheafExtensionByZeroFlatAtOfMem (X := X) U hx)
  · simpa [SheafOfModules.flat_at] using
      (openSubsetStructureSheafExtensionByZeroFlatAtOfNotMem (X := X) U hx)

end AlgebraicGeometry.RingedSpace.ModuleSheaf
