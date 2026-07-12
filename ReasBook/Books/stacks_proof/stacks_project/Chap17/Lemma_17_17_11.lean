import Mathlib
import StacksProject_2024.Chap17.Definition_17_17_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open scoped BigOperators ModuleRestriction

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.17.11:
- primary domain: local factorization of two-step complexes of sheaves of modules on a ringed
  space with flat target, together with the matrix description of maps between finite free
  restrictions;
- sampled owner declarations:
  `SheafOfModules.flat_at`,
  `AlgebraicGeometry.RingedSpace.moduleRestrictionMap`,
  `AlgebraicGeometry.RingedSpace.moduleOverRestrictionMap`,
  `SheafOfModules.freeHomEquiv`;
- best owner abstraction: the core theorem should use the pointwise flatness owner
  `SheafOfModules.flat_at ℱ x` and the restriction-to-open owner
  `AlgebraicGeometry.RingedSpace.moduleRestrictionMap` on `X`, together with the slice
  restriction owner `AlgebraicGeometry.RingedSpace.moduleOverRestrictionMap` on `Over U`; the
  matrix theorem remains a source-facing bridge obtained by unwinding
  `SheafOfModules.freeHomEquiv`;
- primitive data: an open `U`, a point `x ∈ U`, morphisms `α` and `β` with `α ≫ β = 0`, and the
  flat stalk `ℱ_x`;
- derived API: the restricted complex on a neighbourhood `V` and the matrix-family reformulation.

Source/core/bridge triage:
- `source-facing`: the local finite-free factorization statement and its matrix form;
- `core/canonical`: `SheafOfModules.flat_at`, the restriction-map owners, and `freeHomEquiv`;
- `bridge/view`: the matrix-family translation of the factorization statement. -/

variable {X : RingedSpace.{u}} {ℱ : SheafOfModules (RingedSpace.ringCatSheaf X)}

variable (X) (ℱ)

/-- Helper for Lemma 17.17.11: sections of the restricted sheaf `ℱ.over U` are canonically the
same as sections of `ℱ` on the open set `U`. -/
private noncomputable def over_sections_equiv_obj
    (U : Opens X) :
    (ℱ.over U).sections ≃ ℱ.val.obj (op U) where
  toFun s := s.1 (op (Over.mk (𝟙 U)))
  invFun m :=
    (ℱ.over U).val.sectionsMk
      (fun V ↦ (ℱ.over U).val.map ((Over.mkIdTerminal.from V.unop).op) m)
      (fun X Y f ↦ by
        -- Compatibility comes from functoriality along the unique morphisms to the terminal
        -- object `U` in the slice category `Over U`.
        have h :
            (Over.mkIdTerminal.from X.unop).op ≫ f = (Over.mkIdTerminal.from Y.unop).op := by
          apply Quiver.Hom.unop_inj
          simp only [Quiver.Hom.unop_op]
          exact Over.mkIdTerminal.hom_ext
            (f.unop ≫ Over.mkIdTerminal.from X.unop)
            (Over.mkIdTerminal.from Y.unop)
        rw [← PresheafOfModules.map_comp_apply, h])
  left_inv s := by
    -- A section on the slice is determined by its restriction from the terminal object.
    ext V
    simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from V.unop).op)
  right_inv m := by
    -- Evaluating at the terminal object recovers the original section because the unique map is
    -- the identity.
    change (ℱ.over U).val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
    have h : Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
      Over.mkIdTerminal.hom_ext _ _
    simpa using (ℱ.over U).val.congr_map_apply (congrArg Quiver.Hom.op h) m

variable {X ℱ}

/-- Helper for Lemma 17.17.11: a section of the structure sheaf on `U` determines the
corresponding section of the unit module on the slice over `U`. -/
private noncomputable def unit_section_of_ring_section
    (U : Opens X) (r : X.presheaf.obj (op U)) :
    (SheafOfModules.unit (X.ringCatSheaf.over U)).sections :=
  (over_sections_equiv_obj
      (X := X) (ℱ := SheafOfModules.unit (RingedSpace.ringCatSheaf X)) U).symm
    (show (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.obj (op U) from r)

/-- Helper for Lemma 17.17.11: evaluating the unit-module section obtained from `r` recovers `r`
itself. -/
private theorem over_sections_equiv_obj_unit_section_of_ring_section
    (U : Opens X) (r : X.presheaf.obj (op U)) :
    (over_sections_equiv_obj
        (X := X) (ℱ := SheafOfModules.unit (RingedSpace.ringCatSheaf X)) U)
      (unit_section_of_ring_section (X := X) U r) = r := by
  -- The section was defined as the inverse image of `r` under the canonical equivalence.
  exact Equiv.apply_symm_apply
    (over_sections_equiv_obj
      (X := X) (ℱ := SheafOfModules.unit (RingedSpace.ringCatSheaf X)) U) r

/-- Helper for Lemma 17.17.11: applying the inverse terminal-object section equivalence and then
evaluating at `U` recovers the original section. -/
private theorem over_sections_equiv_obj_symm_apply
    (U : Opens X) (m : ℱ.val.obj (op U)) :
    ((over_sections_equiv_obj (X := X) (ℱ := ℱ) U).symm m).1 (op (Over.mk (𝟙 U))) = m := by
  -- The inverse was defined so that evaluation at the terminal object over `U` is exactly `m`.
  exact Equiv.apply_symm_apply (over_sections_equiv_obj (X := X) (ℱ := ℱ) U) m

/-- Helper for Lemma 17.17.11: evaluating the inverse section equivalence on `V : Over U`
restricts the ambient section along `V.hom`. -/
private theorem over_sections_equiv_obj_symm_app
    (U : Opens X) (m : ℱ.val.obj (op U)) (V : Over U) :
    ((over_sections_equiv_obj (X := X) (ℱ := ℱ) U).symm m).1 (op V) =
      ℱ.val.map (show op U ⟶ op V.left from op V.hom) m := by
  -- Proof comment: unfold the inverse section equivalence and identify the terminal restriction
  -- arrow in `Over U` with the structural map `V.hom`.
  change ℱ.val.map (show op U ⟶ op V.left from op (Over.mkIdTerminal.from V).left) m =
    ℱ.val.map (show op U ⟶ op V.left from op V.hom) m
  have hleft : (Over.mkIdTerminal.from V).left = V.hom := by
    simpa using Over.w (Over.mkIdTerminal.from V)
  rw [hleft]

/-- Helper for Lemma 17.17.11: a section over `U` viewed at the terminal object of the slice
over `U`. -/
private abbrev ring_section_at_terminal
    (U : Opens X) (r : X.presheaf.obj (op U)) :
    ↑((X.ringCatSheaf.over U).1.obj (op (Over.mk (𝟙 U)))) :=
  r

/-- Helper for Lemma 17.17.11: the `i`th free basis vector evaluated on the terminal object of the
slice over `U`. -/
private noncomputable abbrev free_basis_at_terminal
    {n : ℕ} (U : Opens X) (i : Fin n) :
    ((SheafOfModules.free.{u} (ULift (Fin n)) :
        SheafOfModules (X.ringCatSheaf.over U)).val.obj (op (Over.mk (𝟙 U)))) :=
  (show ((SheafOfModules.free.{u} (ULift (Fin n)) :
      SheafOfModules (X.ringCatSheaf.over U)).sections) from
    SheafOfModules.freeSection (R := X.ringCatSheaf.over U) (ULift.up i)).1
      (op (Over.mk (𝟙 U)))

/-- Helper for Lemma 17.17.11: the family `f_i` determines the morphism
`\mathcal O_U \to \mathcal O_U^{\oplus n}` on the slice over `U`. -/
private noncomputable def free_morphism_of_ring_family
    {n : ℕ} (U : Opens X) (f : Fin n → X.presheaf.obj (op U)) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      (SheafOfModules.free.{u} (ULift (Fin n)) : SheafOfModules (X.ringCatSheaf.over U)) :=
  ∑ i,
    (SheafOfModules.unitHomEquiv
        (SheafOfModules.unit (X.ringCatSheaf.over U))).symm
      (unit_section_of_ring_section (X := X) U (f i.down)) ≫
      (show SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
          (SheafOfModules.free.{u} (ULift (Fin n)) : SheafOfModules (X.ringCatSheaf.over U))
        from @SheafOfModules.ιFree _ _ _ (X.ringCatSheaf.over U) _ _ _ (ULift (Fin n)) i)

/-- Helper for Lemma 17.17.11: the family `s_i` determines the morphism
`\mathcal O_U^{\oplus n} \to \mathcal F|_U` on the slice over `U`. -/
private noncomputable def module_morphism_of_section_family
    {n : ℕ} (U : Opens X) (s : Fin n → ℱ.val.obj (op U)) :
    (SheafOfModules.free.{u} (ULift (Fin n)) : SheafOfModules (X.ringCatSheaf.over U)) ⟶
      ℱ.over U :=
  (SheafOfModules.freeHomEquiv (ℱ.over U)).symm
    (fun i ↦ (over_sections_equiv_obj (X := X) (ℱ := ℱ) U).symm (s i.down))

/-- Helper for Lemma 17.17.11: the free-basis component of the morphism attached to the family
`s_i` is exactly the original section `s_i`. -/
private theorem freeHomEquiv_module_morphism_of_section_family
    {n : ℕ} (U : Opens X) (s : Fin n → ℱ.val.obj (op U)) (i : ULift (Fin n)) :
    (SheafOfModules.freeHomEquiv (ℱ.over U)
        (module_morphism_of_section_family (X := X) (ℱ := ℱ) U s) i) =
      (over_sections_equiv_obj (X := X) (ℱ := ℱ) U).symm (s i.down) := by
  -- This is the defining property of `freeHomEquiv.symm`.
  simp [module_morphism_of_section_family]

/-- Helper for Lemma 17.17.11: the morphism built from the family `s_i` sends the `i`th free
basis section to the section corresponding to `s_i`. -/
private theorem sectionsMap_module_morphism_of_section_family_freeSection
    {n : ℕ} (U : Opens X) (s : Fin n → ℱ.val.obj (op U)) (i : ULift (Fin n)) :
    SheafOfModules.sectionsMap
        (module_morphism_of_section_family (X := X) (ℱ := ℱ) U s)
        (show ((SheafOfModules.free.{u} (ULift (Fin n)) :
            SheafOfModules (X.ringCatSheaf.over U)).sections) from
          SheafOfModules.freeSection (R := X.ringCatSheaf.over U) i) =
      (over_sections_equiv_obj (X := X) (ℱ := ℱ) U).symm (s i.down) := by
  -- The basis-section formula is the defining property of `freeHomEquiv.symm`.
  simpa [module_morphism_of_section_family] using
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (f := fun j : ULift (Fin n) ↦
        (over_sections_equiv_obj (X := X) (ℱ := ℱ) U).symm (s j.down))
      (R := X.ringCatSheaf.over U) i)

/-- Helper for Lemma 17.17.11: evaluating the image of the `i`th basis section on the terminal
object over `U` recovers the original section `s_i`. -/
private theorem module_morphism_of_section_family_app_terminal_freeSection
    {n : ℕ} (U : Opens X) (s : Fin n → ℱ.val.obj (op U)) (i : ULift (Fin n)) :
    ((module_morphism_of_section_family (X := X) (ℱ := ℱ) U s).val.app
        (op (Over.mk (𝟙 U))))
      ((show ((SheafOfModules.free.{u} (ULift (Fin n)) :
          SheafOfModules (X.ringCatSheaf.over U)).sections) from
        SheafOfModules.freeSection (R := X.ringCatSheaf.over U) i).1
          (op (Over.mk (𝟙 U)))) = s i.down := by
  -- Evaluate the basis-section identity at the terminal object of the slice over `U`.
  have h :=
    sectionsMap_module_morphism_of_section_family_freeSection
      (X := X) (ℱ := ℱ) U s i
  simpa [over_sections_equiv_obj_symm_apply] using
    congrArg (fun t : (ℱ.over U).sections ↦ t.1 (op (Over.mk (𝟙 U)))) h

/-- Helper for Lemma 17.17.11: `unitHomEquiv` is computed by evaluating the corresponding
unit morphism on the terminal-object section `1`. -/
private theorem unitHomEquiv_apply_terminal
    {U : Opens X} (M : SheafOfModules (X.ringCatSheaf.over U))
    (φ : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ M) :
    (SheafOfModules.unitHomEquiv M φ).1 (op (Over.mk (𝟙 U))) =
      (φ.val.app (op (Over.mk (𝟙 U)))) (ring_section_at_terminal (X := X) U 1) := by
  -- Evaluate `unitHomEquiv` at the terminal object; by definition it is evaluation on `1`.
  rfl

/-- Helper for Lemma 17.17.11: evaluating the morphism attached to the coefficient family `f_i`
on the terminal-object section `1` gives the expected linear combination of free basis vectors. -/
private theorem free_morphism_of_ring_family_app_terminal_one
    {n : ℕ} (U : Opens X) (f : Fin n → X.presheaf.obj (op U)) :
    ((free_morphism_of_ring_family (X := X) U f).val.app (op (Over.mk (𝟙 U))))
        (ring_section_at_terminal (X := X) U 1) =
      ∑ i, ring_section_at_terminal (X := X) U (f i) • free_basis_at_terminal (X := X) U i := by
  rw [free_morphism_of_ring_family, map_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  let gi :
      SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
        SheafOfModules.unit (X.ringCatSheaf.over U) :=
    (SheafOfModules.unitHomEquiv
      (SheafOfModules.unit (X.ringCatSheaf.over U))).symm
        (unit_section_of_ring_section (X := X) U (f i.down))
  have hgi :
      (gi.val.app (op (Over.mk (𝟙 U)))) (ring_section_at_terminal (X := X) U 1) =
        ring_section_at_terminal (X := X) U (f i.down) := by
    -- Proof comment: the unit morphism corresponding to `f_i` evaluates to `f_i` on the terminal
    -- section `1`.
    have hsection :
        (SheafOfModules.unitHomEquiv
            (SheafOfModules.unit (X.ringCatSheaf.over U)) gi).1
            (op (Over.mk (𝟙 U))) =
          ring_section_at_terminal (X := X) U (f i.down) := by
      simpa [gi, ring_section_at_terminal, unit_section_of_ring_section] using
        (over_sections_equiv_obj_symm_apply
          (X := X) (ℱ := SheafOfModules.unit (RingedSpace.ringCatSheaf X))
          U (f i.down))
    exact (unitHomEquiv_apply_terminal
        (X := X)
        (M := SheafOfModules.unit (X.ringCatSheaf.over U))
        gi).symm.trans hsection
  have hbasis :
      ((SheafOfModules.ιFree (R := X.ringCatSheaf.over U) (ULift.up i)).val.app
          (op (Over.mk (𝟙 U))))
        (ring_section_at_terminal (X := X) U 1) =
          free_basis_at_terminal (X := X) U i := by
    -- Proof comment: the `i`th basis inclusion evaluates to the `i`th terminal free basis
    -- vector.
    simpa [free_basis_at_terminal, ring_section_at_terminal] using
      (unitHomEquiv_apply_terminal
        (X := X)
        (M := (SheafOfModules.free.{u} (ULift (Fin n)) :
          SheafOfModules (X.ringCatSheaf.over U)))
        (SheafOfModules.ιFree (R := X.ringCatSheaf.over U) (ULift.up i))).symm
  -- Proof comment: evaluate the composite summand on `1`, then use linearity of the basis
  -- inclusion to pull out the coefficient `f_i`.
  change
    ((SheafOfModules.ιFree (R := X.ringCatSheaf.over U) (ULift.up i)).val.app
        (op (Over.mk (𝟙 U))))
      ((gi.val.app (op (Over.mk (𝟙 U)))) (ring_section_at_terminal (X := X) U 1)) =
        ring_section_at_terminal (X := X) U (f i) • free_basis_at_terminal (X := X) U i
  rw [hgi]
  have hscalar :
      ring_section_at_terminal (X := X) U (f i) =
        ring_section_at_terminal (X := X) U (f i) •
          ring_section_at_terminal (X := X) U (1 : X.presheaf.obj (op U)) := by
    simp [ring_section_at_terminal]
  rw [hscalar, map_smul, hbasis]

/-- Helper for Lemma 17.17.11: a unit morphism into the finite free sheaf is determined by the
terminal linear combination of the free basis vectors. -/
private theorem unit_morphism_eq_free_morphism_of_terminal_linear_combination
    {n : ℕ} (U : Opens X)
    (α : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      (SheafOfModules.free.{u} (ULift (Fin n)) : SheafOfModules (X.ringCatSheaf.over U)))
    (f : Fin n → X.presheaf.obj (op U))
    (hα :
      (SheafOfModules.unitHomEquiv
          (SheafOfModules.free.{u} (ULift (Fin n)) :
            SheafOfModules (X.ringCatSheaf.over U)) α).1
          (op (Over.mk (𝟙 U))) =
        ∑ i, ring_section_at_terminal (X := X) U (f i) •
          free_basis_at_terminal (X := X) U i) :
    α = free_morphism_of_ring_family (X := X) U f := by
  let M : SheafOfModules (X.ringCatSheaf.over U) :=
    (SheafOfModules.free.{u} (ULift (Fin n)) : SheafOfModules (X.ringCatSheaf.over U))
  let sα : M.sections := SheafOfModules.unitHomEquiv M α
  let sf : M.sections := SheafOfModules.unitHomEquiv M (free_morphism_of_ring_family (X := X) U f)
  -- A section on the slice is determined by its terminal value.
  apply (SheafOfModules.unitHomEquiv M).injective
  ext V
  -- Compare the two sections in the direction matching the slice restriction formula.
  symm
  have hterminal : sα.1 (op (Over.mk (𝟙 U))) = sf.1 (op (Over.mk (𝟙 U))) := by
    -- Rewrite the target morphism through its terminal evaluation formula.
    rw [show sα.1 (op (Over.mk (𝟙 U))) =
        (SheafOfModules.unitHomEquiv M α).1 (op (Over.mk (𝟙 U))) by rfl]
    rw [show sf.1 (op (Over.mk (𝟙 U))) =
        (SheafOfModules.unitHomEquiv M
          (free_morphism_of_ring_family (X := X) U f)).1 (op (Over.mk (𝟙 U))) by rfl]
    rw [hα, unitHomEquiv_apply_terminal]
    exact (free_morphism_of_ring_family_app_terminal_one (X := X) U f).symm
  have hαV :
      sα.1 V =
        (M.val.map ((Over.mkIdTerminal.from V.unop).op))
          (sα.1 (op (Over.mk (𝟙 U)))) := by
    -- Any section on the slice is the restriction of its terminal value.
    symm
    simpa [sα] using PresheafOfModules.sections_property sα ((Over.mkIdTerminal.from V.unop).op)
  have hsfV :
      (M.val.map ((Over.mkIdTerminal.from V.unop).op))
        (sf.1 (op (Over.mk (𝟙 U)))) = sf.1 V := by
    -- The explicit free-morphism section is also determined by its terminal value.
    simpa [sf] using PresheafOfModules.sections_property sf ((Over.mkIdTerminal.from V.unop).op)
  -- Both sections are restrictions of the same terminal value.
  exact hsfV.symm.trans <| by
    rw [← hterminal]
    exact hαV.symm

/-- Helper for Lemma 17.17.11: the morphism built from the section family `s_i` sends a terminal
linear combination of free basis vectors to the corresponding linear combination of the `s_i`. -/
private theorem module_morphism_of_section_family_app_terminal_linear_combination
    {n : ℕ} (U : Opens X) (s : Fin n → ℱ.val.obj (op U))
    (c : Fin n → X.presheaf.obj (op U)) :
    ((module_morphism_of_section_family (X := X) (ℱ := ℱ) U s).val.app
        (op (Over.mk (𝟙 U))))
      (∑ i, ring_section_at_terminal (X := X) U (c i) • free_basis_at_terminal (X := X) U i) =
        ∑ i, c i • s i := by
  -- Linearity at the terminal object reduces the claim to the basis computation proved above.
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [map_smul]
  simpa [ring_section_at_terminal, free_basis_at_terminal] using
    congrArg (fun t : ℱ.val.obj (op U) ↦ c i • t)
      (module_morphism_of_section_family_app_terminal_freeSection
        (X := X) (ℱ := ℱ) U s (ULift.up i))

/-- Helper for Lemma 17.17.11: the explicit coefficient and section families realize the
categorical complex relation as the source relation `∑ i, f_i • s_i`. -/
private theorem complex_section_relation_of_unit_free_homs
    {n : ℕ} (U : Opens X)
    (f : Fin n → X.presheaf.obj (op U))
    (s : Fin n → ℱ.val.obj (op U)) :
    (over_sections_equiv_obj (X := X) (ℱ := ℱ) U)
      (SheafOfModules.unitHomEquiv (ℱ.over U)
        (free_morphism_of_ring_family (X := X) U f ≫
          module_morphism_of_section_family (X := X) (ℱ := ℱ) U s)) =
        ∑ i, f i • s i := by
  -- Rewrite the composite through `unitHomEquiv`, then evaluate it at the terminal object.
  change (over_sections_equiv_obj (X := X) (ℱ := ℱ) U)
      (SheafOfModules.sectionsMap
        (module_morphism_of_section_family (X := X) (ℱ := ℱ) U s)
        (SheafOfModules.unitHomEquiv
          (SheafOfModules.free.{u} (ULift (Fin n)) :
            SheafOfModules (X.ringCatSheaf.over U))
          (free_morphism_of_ring_family (X := X) U f))) =
      ∑ i, f i • s i
  change ((module_morphism_of_section_family (X := X) (ℱ := ℱ) U s).val.app
      (op (Over.mk (𝟙 U))))
    (((SheafOfModules.unitHomEquiv
        (SheafOfModules.free.{u} (ULift (Fin n)) :
          SheafOfModules (X.ringCatSheaf.over U)))
      (free_morphism_of_ring_family (X := X) U f)).1 (op (Over.mk (𝟙 U)))) =
      ∑ i, f i • s i
  -- The `α` side gives the free-basis combination and the `β` side evaluates it to `∑ f_i • s_i`.
  rw [show (((SheafOfModules.unitHomEquiv
        (SheafOfModules.free.{u} (ULift (Fin n)) :
          SheafOfModules (X.ringCatSheaf.over U)))
      (free_morphism_of_ring_family (X := X) U f)).1 (op (Over.mk (𝟙 U)))) =
      ((free_morphism_of_ring_family (X := X) U f).val.app (op (Over.mk (𝟙 U))))
        (ring_section_at_terminal (X := X) U 1) by
        rfl]
  rw [free_morphism_of_ring_family_app_terminal_one]
  exact module_morphism_of_section_family_app_terminal_linear_combination
    (X := X) (ℱ := ℱ) U s f

/-- Helper for Lemma 17.17.11: sections of the restriction of a sheaf on `Over U` to
`V : Over U` are canonically identified with the value of the original sheaf on `V`. -/
private noncomputable def slice_over_sections_equiv_obj
    {U : Opens X} (M : SheafOfModules (X.ringCatSheaf.over U)) (V : Over U) :
    (M.over V).sections ≃ M.val.obj (op V) where
  toFun s := s.1 (op (Over.mk (𝟙 V)))
  invFun m :=
    (M.over V).val.sectionsMk
      (fun W ↦ (M.over V).val.map ((Over.mkIdTerminal.from W.unop).op) m)
      (fun W W' f ↦ by
        -- Compatibility again comes from the unique arrows to the terminal object in `Over V`.
        have h :
            (Over.mkIdTerminal.from W.unop).op ≫ f = (Over.mkIdTerminal.from W'.unop).op := by
          apply Quiver.Hom.unop_inj
          simp only [Quiver.Hom.unop_op]
          exact Over.mkIdTerminal.hom_ext
            (f.unop ≫ Over.mkIdTerminal.from W.unop)
            (Over.mkIdTerminal.from W'.unop)
        rw [← PresheafOfModules.map_comp_apply, h])
  left_inv s := by
    -- A section on the iterated slice is determined by its restriction from the terminal object.
    ext W
    simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from W.unop).op)
  right_inv m := by
    -- Evaluating at the terminal object of `Over V` recovers the original section on `V`.
    change (M.over V).val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 V))).op) m = m
    have h : Over.mkIdTerminal.from (Over.mk (𝟙 V)) = 𝟙 (Over.mk (𝟙 V)) :=
      Over.mkIdTerminal.hom_ext _ _
    simpa using (M.over V).val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 17.17.11: restricting a morphism on `Over U` to `V` and evaluating at the
terminal object of `Over V` is the same as evaluating the original morphism on `V`. -/
private theorem moduleOverRestrictionMap_app_terminal
    {U : Opens X} {M N : SheafOfModules (X.ringCatSheaf.over U)}
    (ψ : M ⟶ N) (V : Over U) :
    (RingedSpace.moduleOverRestrictionMap V ψ).val.app (op (Over.mk (𝟙 V))) = ψ.val.app (op V) := by
  -- On the terminal object of the iterated slice, restriction is definitionally the original
  -- component on `V`.
  ext m
  rfl

/-- Helper for Lemma 17.17.11: under the canonical section equivalence on `Over V`, the
restriction of a morphism acts by the original component on `V`. -/
private theorem slice_over_sections_equiv_obj_sectionsMap
    {U : Opens X} {M N : SheafOfModules (X.ringCatSheaf.over U)}
    (ψ : M ⟶ N) (V : Over U) (s : (M.over V).sections) :
    (slice_over_sections_equiv_obj (X := X) N V)
      (SheafOfModules.sectionsMap (RingedSpace.moduleOverRestrictionMap V ψ) s) =
        (ψ.val.app (op V)) ((slice_over_sections_equiv_obj (X := X) M V) s) := by
  -- Evaluate both sides at the terminal object of `Over V`.
  change ((RingedSpace.moduleOverRestrictionMap V ψ).val.app (op (Over.mk (𝟙 V))))
      (s.1 (op (Over.mk (𝟙 V)))) =
    (ψ.val.app (op V)) (s.1 (op (Over.mk (𝟙 V))))
  exact congrArg
    (fun f : M.val.obj (op V) ⟶ N.val.obj (op V) ↦ f (s.1 (op (Over.mk (𝟙 V)))))
    (moduleOverRestrictionMap_app_terminal (X := X) ψ V)

/-- Helper for Lemma 17.17.11: the inverse of the iterated-slice section equivalence is natural
in the restricted morphism. -/
private theorem sectionsMap_slice_over_sections_equiv_obj_symm
    {U : Opens X} {M N : SheafOfModules (X.ringCatSheaf.over U)}
    (ψ : M ⟶ N) (V : Over U) (m : M.val.obj (op V)) :
    SheafOfModules.sectionsMap (RingedSpace.moduleOverRestrictionMap V ψ)
        ((slice_over_sections_equiv_obj (X := X) M V).symm m) =
      (slice_over_sections_equiv_obj (X := X) N V).symm ((ψ.val.app (op V)) m) := by
  -- Compare both sections after evaluating them at the terminal object of the iterated slice.
  apply (slice_over_sections_equiv_obj (X := X) N V).injective
  rw [slice_over_sections_equiv_obj_sectionsMap]
  simp

/-- Helper for Lemma 17.17.11: a morphism out of a free sheaf on the iterated slice is determined
by its values on the free basis sections. -/
private theorem moduleHom_eq_of_freeSection_eq
    {U : Opens X} {V : Over U} {I : Type u}
    {M : SheafOfModules ((X.ringCatSheaf.over U).over V)}
    {f g : (SheafOfModules.free.{u} I :
      SheafOfModules ((X.ringCatSheaf.over U).over V)) ⟶ M}
    (hfg : ∀ i : I,
      SheafOfModules.sectionsMap f
          (SheafOfModules.freeSection (R := (X.ringCatSheaf.over U).over V) i) =
        SheafOfModules.sectionsMap g
          (SheafOfModules.freeSection (R := (X.ringCatSheaf.over U).over V) i)) :
    f = g := by
  -- `freeHomEquiv` identifies a morphism with the images of the basis sections.
  apply (SheafOfModules.freeHomEquiv M).injective
  funext i
  exact hfg i

/-- Helper for Lemma 17.17.11: restriction to the slice over `V : Over U` is the canonical
pushforward functor on module sheaves over `Over U`. -/
private abbrev overRestrictionFunctor
    {U : Opens X} (V : Over U) :
    SheafOfModules (X.ringCatSheaf.over U) ⥤
      SheafOfModules ((X.ringCatSheaf.over U).over V) :=
  SheafOfModules.pushforward (𝟙 ((X.ringCatSheaf.over U).over V))

/-- Helper for Lemma 17.17.11: `mapFree` identifies the restriction of a free sheaf on `Over U`
with the canonical free sheaf on the slice over `V`. -/
private abbrev overRestrictionFreeIso
    {U : Opens X} (V : Over U) (I : Type u) :
    (overRestrictionFunctor (X := X) V).obj
        (SheafOfModules.free.{u} I : SheafOfModules (X.ringCatSheaf.over U)) ≅
      (SheafOfModules.free.{u} I :
        SheafOfModules ((X.ringCatSheaf.over U).over V)) :=
  SheafOfModules.mapFree
    (overRestrictionFunctor (X := X) V)
    (Iso.refl (SheafOfModules.unit ((X.ringCatSheaf.over U).over V)))
    I

/-- Helper for Lemma 17.17.11: the `mapFree` comparison carries each ambient free basis morphism
to the corresponding basis morphism on the iterated slice. -/
private theorem overRestrictionFreeIso_hom_ιFree
    {U : Opens X} (V : Over U) (I : Type u) (i : I) :
    (overRestrictionFunctor (X := X) V).map
        (SheafOfModules.ιFree (R := X.ringCatSheaf.over U) i) ≫
        (overRestrictionFreeIso (X := X) V I).hom =
      SheafOfModules.ιFree (R := (X.ringCatSheaf.over U).over V) i := by
  -- Proof comment: this is the basis-vector computation built into `mapFree`.
  simpa [overRestrictionFunctor, overRestrictionFreeIso] using
    (SheafOfModules.map_ιFree_mapFree_hom
      (F := SheafOfModules.pushforward (𝟙 ((X.ringCatSheaf.over U).over V)))
      (η := Iso.refl (SheafOfModules.unit ((X.ringCatSheaf.over U).over V)))
      (I := I) (i := i))

/-- Helper for Lemma 17.17.11: the inverse `mapFree` transport sends the slice free basis section
to the restricted ambient free basis section. -/
private theorem restrictedFreeBasisTransport
    {U : Opens X} (I : Type u) (V : Over U) (i : I) :
    SheafOfModules.sectionsMap
        ((overRestrictionFreeIso (X := X) V I).inv)
        (SheafOfModules.freeSection (R := (X.ringCatSheaf.over U).over V) i) =
      (slice_over_sections_equiv_obj (X := X)
          (SheafOfModules.free.{u} I : SheafOfModules (X.ringCatSheaf.over U)) V).symm
        ((SheafOfModules.freeSection (R := X.ringCatSheaf.over U) i).1 (op V)) := by
  -- Route correction: avoid unfolding the iterated-slice section equivalence by hand.
  -- The stable route is to compare the basis inclusions through `mapFree.hom` and then read the
  -- resulting section equality through `slice_over_sections_equiv_obj`.
  let e := overRestrictionFreeIso (X := X) V I
  have hiota :
      (overRestrictionFunctor (X := X) V).map
          (SheafOfModules.ιFree (R := X.ringCatSheaf.over U) i) =
        SheafOfModules.ιFree (R := (X.ringCatSheaf.over U).over V) i ≫ e.inv := by
    -- Compare the basis inclusions through `mapFree.hom` and cancel the isomorphism.
    apply (cancel_mono e.hom).1
    simpa [Category.assoc] using overRestrictionFreeIso_hom_ιFree (X := X) V I i
  calc
    SheafOfModules.sectionsMap e.inv
        (SheafOfModules.freeSection (R := (X.ringCatSheaf.over U).over V) i) =
      SheafOfModules.unitHomEquiv
        (((SheafOfModules.free.{u} I : SheafOfModules (X.ringCatSheaf.over U)).over V))
        (SheafOfModules.ιFree (R := (X.ringCatSheaf.over U).over V) i ≫ e.inv) := by
          rfl
    _ =
      SheafOfModules.unitHomEquiv
        (((SheafOfModules.free.{u} I : SheafOfModules (X.ringCatSheaf.over U)).over V))
        ((overRestrictionFunctor (X := X) V).map
          (SheafOfModules.ιFree (R := X.ringCatSheaf.over U) i)) := by
          rw [← hiota]
  apply (slice_over_sections_equiv_obj (X := X)
      (SheafOfModules.free.{u} I : SheafOfModules (X.ringCatSheaf.over U)) V).injective
  -- Evaluating the restricted ambient basis morphism at the terminal object of `Over V` gives
  -- the ambient basis section restricted to `V`.
  rfl

/-- Helper for Lemma 17.17.11: transporting the restricted ambient free basis section back across
`mapFree.hom` recovers the tautological free basis section on the iterated slice. -/
private theorem restrictedAmbientBasisTransport
    {U : Opens X} (I : Type u) (V : Over U) (i : I) :
    SheafOfModules.sectionsMap
        ((overRestrictionFreeIso (X := X) V I).hom)
        ((slice_over_sections_equiv_obj (X := X)
            (SheafOfModules.free.{u} I : SheafOfModules (X.ringCatSheaf.over U)) V).symm
          ((SheafOfModules.freeSection (R := X.ringCatSheaf.over U) i).1 (op V))) =
      SheafOfModules.freeSection (R := (X.ringCatSheaf.over U).over V) i := by
  let e := overRestrictionFreeIso (X := X) V I
  -- Proof comment: apply `sectionsMap e.hom` to the inverse-transport formula and cancel the
  -- section-level isomorphism on the free sheaf.
  have h :=
    congrArg (SheafOfModules.sectionsMap e.hom)
      (restrictedFreeBasisTransport (X := X) I V i)
  simpa [e, SheafOfModules.sectionsMap_comp] using h

/-- Helper for Lemma 17.17.11: evaluating a unit morphism on an arbitrary slice object `V`
computes the corresponding section at `V` by applying the component morphism to `1`. -/
private theorem unitHomEquiv_apply
    {U : Opens X} (M : SheafOfModules (X.ringCatSheaf.over U))
    (φ : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ M) (V : Over U) :
    (SheafOfModules.unitHomEquiv M φ).1 (op V) =
      (φ.val.app (op V)) (show ↑((X.ringCatSheaf.over U).1.obj (op V)) from 1) := by
  -- `unitHomEquiv` is defined by evaluation on the distinguished section `1`.
  rfl

/-- Helper for Lemma 17.17.11: the ring-section-induced unit section restricts along `V.hom` to
the corresponding ring section on `V.left`. -/
private theorem unit_section_of_ring_section_app
    (U : Opens X) (r : X.presheaf.obj (op U)) (V : Over U) :
    (unit_section_of_ring_section (X := X) U r).1 (op V) =
      X.presheaf.map (show op U ⟶ op V.left from op V.hom) r := by
  -- Proof comment: this is the general section-restriction formula specialized to the unit
  -- module sheaf.
  simpa [unit_section_of_ring_section] using
    over_sections_equiv_obj_symm_app
      (X := X) (ℱ := SheafOfModules.unit (RingedSpace.ringCatSheaf X)) U r V

/-- Helper for Lemma 17.17.11: evaluating the morphism attached to the family `s_i` on the
restricted `i`th basis section over `V` gives the restricted section `s_i|_V`. -/
private theorem module_morphism_of_section_family_app_freeSection
    {n : ℕ} (U : Opens X) (s : Fin n → ℱ.val.obj (op U))
    (V : Over U) (i : ULift (Fin n)) :
    ((module_morphism_of_section_family (X := X) (ℱ := ℱ) U s).val.app (op V))
      ((SheafOfModules.freeSection (R := X.ringCatSheaf.over U) i).1 (op V)) =
        ℱ.val.map (show op U ⟶ op V.left from op V.hom) (s i.down) := by
  have h :=
    sectionsMap_module_morphism_of_section_family_freeSection
      (X := X) (ℱ := ℱ) U s i
  -- Proof comment: evaluate the section equality at `V` and rewrite the inverse section
  -- equivalence on the right-hand side as the ambient restriction map along `V.hom`.
  simpa [over_sections_equiv_obj_symm_app] using
    congrArg (fun t : (ℱ.over U).sections ↦ t.1 (op V)) h

/-- Helper for Lemma 17.17.11: evaluating the morphism attached to the coefficient family `f_i`
on the section `1` over `V` gives the restricted linear combination of the free basis sections. -/
private theorem free_morphism_of_ring_family_app_one
    {n : ℕ} (U : Opens X) (f : Fin n → X.presheaf.obj (op U)) (V : Over U) :
    ((free_morphism_of_ring_family (X := X) U f).val.app (op V))
      (show ↑((X.ringCatSheaf.over U).1.obj (op V)) from 1) =
        ∑ i, (show ↑((X.ringCatSheaf.over U).1.obj (op V)) from
          X.presheaf.map (show op U ⟶ op V.left from op V.hom) (f i)) •
          (show ↑(((SheafOfModules.free.{u} (ULift (Fin n)) :
              SheafOfModules (X.ringCatSheaf.over U)).val.obj (op V))) from
            ((SheafOfModules.freeSection (R := X.ringCatSheaf.over U) (ULift.up i)).1 (op V))) := by
  rw [free_morphism_of_ring_family, map_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  let gi :
      SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
        SheafOfModules.unit (X.ringCatSheaf.over U) :=
    (SheafOfModules.unitHomEquiv
      (SheafOfModules.unit (X.ringCatSheaf.over U))).symm
        (unit_section_of_ring_section (X := X) U (f i.down))
  have hgi :
      (gi.val.app (op V)) (show ↑((X.ringCatSheaf.over U).1.obj (op V)) from 1) =
        (show ↑((X.ringCatSheaf.over U).1.obj (op V)) from
          X.presheaf.map (show op U ⟶ op V.left from op V.hom) (f i.down)) := by
    -- Proof comment: evaluate the unit morphism corresponding to `f_i` on the distinguished
    -- section `1`, then rewrite the resulting section through the ambient restriction map.
    have hsection :
        (SheafOfModules.unitHomEquiv
            (SheafOfModules.unit (X.ringCatSheaf.over U)) gi).1 (op V) =
          X.presheaf.map (show op U ⟶ op V.left from op V.hom) (f i.down) := by
      simpa [gi] using
        unit_section_of_ring_section_app (X := X) U (f i.down) V
    exact (unitHomEquiv_apply
        (X := X)
        (M := SheafOfModules.unit (X.ringCatSheaf.over U))
        gi V).symm.trans hsection
  have hbasis :
      ((SheafOfModules.ιFree (R := X.ringCatSheaf.over U) (ULift.up i)).val.app (op V))
        (show ↑((X.ringCatSheaf.over U).1.obj (op V)) from 1) =
          (show ↑(((SheafOfModules.free.{u} (ULift (Fin n)) :
              SheafOfModules (X.ringCatSheaf.over U)).val.obj (op V))) from
            ((SheafOfModules.freeSection (R := X.ringCatSheaf.over U) (ULift.up i)).1 (op V)) ) := by
    -- Proof comment: the `i`th basis inclusion evaluated on `1` is the `i`th free basis section
    -- over `V`.
    simpa using
      (unitHomEquiv_apply
        (X := X)
        (M := (SheafOfModules.free.{u} (ULift (Fin n)) :
          SheafOfModules (X.ringCatSheaf.over U)))
        (SheafOfModules.ιFree (R := X.ringCatSheaf.over U) (ULift.up i))
        V).symm
  -- Proof comment: as at the terminal object, evaluate the composite summand on `1` and then
  -- use linearity of the basis inclusion to pull out the restricted coefficient.
  change
    ((SheafOfModules.ιFree (R := X.ringCatSheaf.over U) (ULift.up i)).val.app (op V))
      ((gi.val.app (op V)) (show ↑((X.ringCatSheaf.over U).1.obj (op V)) from 1)) =
        (show ↑((X.ringCatSheaf.over U).1.obj (op V)) from
          X.presheaf.map (show op U ⟶ op V.left from op V.hom) (f i)) •
          (show ↑(((SheafOfModules.free.{u} (ULift (Fin n)) :
              SheafOfModules (X.ringCatSheaf.over U)).val.obj (op V))) from
            ((SheafOfModules.freeSection (R := X.ringCatSheaf.over U) (ULift.up i)).1 (op V)))
  rw [hgi]
  have hscalar :
      (show ↑((X.ringCatSheaf.over U).1.obj (op V)) from
        X.presheaf.map (show op U ⟶ op V.left from op V.hom) (f i)) =
        (show ↑((X.ringCatSheaf.over U).1.obj (op V)) from
          X.presheaf.map (show op U ⟶ op V.left from op V.hom) (f i)) •
          (show ↑((X.ringCatSheaf.over U).1.obj (op V)) from 1) := by
    simp
  rw [hscalar, map_smul, hbasis]

/-- Helper for Lemma 17.17.11: taking the germ of a section over `U` is semilinear over the stalk
ring at `x`. -/
private def stalkGermLinear
    (x : X) (U : Opens X) (hx : x ∈ U) :
    ℱ.val.obj (op U) →ₛₗ[(X.presheaf.germ U x hx).hom] ↑(RingedSpace.stalkModuleCat ℱ x) where
  toFun s := TopCat.Presheaf.germ ℱ.val.presheaf U x hx s
  map_add' := by
    intro s t
    -- Proof comment: the stalk germ map is additive on sections.
    simpa using (TopCat.Presheaf.germ ℱ.val.presheaf U x hx).hom.map_add s t
  map_smul' := by
    intro r s
    -- Proof comment: `PresheafOfModules.germ_smul` identifies the germ of a scalar multiple with
    -- the scalar multiple of the germ.
    simpa using PresheafOfModules.germ_smul ℱ.val x U hx r s

/-- Helper for Lemma 17.17.11: a section relation `∑ f_i • s_i = 0` on `U` induces the
corresponding stalk relation at the point `x`. -/
private theorem stalkRelationOfSectionFamily
    {U : Opens X} {n : ℕ}
    (f : Fin n → X.presheaf.obj (op U))
    (s : Fin n → ℱ.val.obj (op U))
    (x : X) (hx : x ∈ U)
    (hcomplex : ∑ i, f i • s i = 0) :
    ∑ i, TopCat.Presheaf.germ X.presheaf U x hx (f i) •
        TopCat.Presheaf.germ ℱ.val.presheaf U x hx (s i) = 0 := by
  let g := stalkGermLinear (X := X) (ℱ := ℱ) x U hx
  have hg : g (∑ i, f i • s i) = g 0 := congrArg g hcomplex
  -- Proof comment: apply the semilinear germ map to the section relation and expand the image of
  -- the finite sum termwise.
  calc
    ∑ i, TopCat.Presheaf.germ X.presheaf U x hx (f i) •
        TopCat.Presheaf.germ ℱ.val.presheaf U x hx (s i) =
      ∑ i, g (f i • s i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa [g, stalkGermLinear] using ((g.map_smulₛₗ (f i) (s i)).symm)
    _ = g (∑ i, f i • s i) := by
      symm
      rw [map_sum]
    _ = g 0 := hg
    _ = 0 := by
      simpa [g, stalkGermLinear] using g.map_zero

/-- Helper for Lemma 17.17.11: flatness of the stalk turns the stalk relation into finite stalk
matrix data. -/
private theorem existsStalkFactorizationDataOfComplexOfFlat
    {U : Opens X} {n : ℕ}
    (f : Fin n → X.presheaf.obj (op U))
    (s : Fin n → ℱ.val.obj (op U))
    (hcomplex : ∑ i, f i • s i = 0)
    (x : X) (hx : x ∈ U) (hflat : ℱ.flat_at x) :
    ∃ (m : ℕ)
      (A : Fin n → Fin m → X.presheaf.stalk x)
      (t : Fin m → RingedSpace.stalkModuleCat ℱ x),
        (∀ i,
          TopCat.Presheaf.germ ℱ.val.presheaf U x hx (s i) =
            ∑ j, A i j • t j) ∧
          ∀ j, ∑ i, TopCat.Presheaf.germ X.presheaf U x hx (f i) * A i j = 0 := by
  let R : Type u := X.presheaf.stalk x
  let M : Type u := ↑(RingedSpace.stalkModuleCat ℱ x)
  let _ : CommRing R := inferInstance
  let _ : AddCommGroup M := inferInstance
  let _ : Module R M := inferInstance
  let _ : Module.Flat R M := hflat
  have hstalk :
      ∑ i, TopCat.Presheaf.germ X.presheaf U x hx (f i) •
          TopCat.Presheaf.germ ℱ.val.presheaf U x hx (s i) = 0 :=
    stalkRelationOfSectionFamily (X := X) (ℱ := ℱ) f s x hx hcomplex
  -- Proof comment: apply the flat trivial-relation theorem directly in the stalk module.
  rcases Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
      (R := R) (M := M)
      (f := fun i ↦ TopCat.Presheaf.germ X.presheaf U x hx (f i))
      (x := fun i ↦ TopCat.Presheaf.germ ℱ.val.presheaf U x hx (s i))
      hstalk with
    ⟨m, A, t, hs, hA⟩
  exact ⟨m, A, t, hs, hA⟩

/-- Helper for Lemma 17.17.11: finitely many stalk coefficients and stalk generators admit
simultaneous representatives on one common neighborhood of `x`. -/
private theorem existsCommonOpenWithStalkRepresentatives
    {U : Opens X} {n m : ℕ}
    (f : Fin n → X.presheaf.obj (op U))
    (s : Fin n → ℱ.val.obj (op U))
    (x : X) (hx : x ∈ U)
    (A : Fin n → Fin m → X.presheaf.stalk x)
    (t : Fin m → RingedSpace.stalkModuleCat ℱ x)
    :
    ∃ (W : Opens X) (_ : x ∈ W) (hWU : W ≤ U)
      (A_W : Fin n → Fin m → X.presheaf.obj (op W))
      (t_W : Fin m → ℱ.val.obj (op W)),
        (∀ i j, TopCat.Presheaf.germ X.presheaf W x ‹x ∈ W› (A_W i j) = A i j) ∧
          ∀ j, TopCat.Presheaf.germ ℱ.val.presheaf W x ‹x ∈ W› (t_W j) = t j := by
  let _ := f
  let _ := s
  choose UA hxUA a ha using
    fun i : Fin n => fun j : Fin m ↦ TopCat.Presheaf.germ_exist X.presheaf x (A i j)
  choose Ut hxUt tU ht using
    fun j : Fin m ↦ TopCat.Presheaf.germ_exist ℱ.val.presheaf x (t j)
  let WA : Opens X := ⨅ i : Fin n, ⨅ j : Fin m, UA i j
  let Wt : Opens X := ⨅ j : Fin m, Ut j
  let W : Opens X := U ⊓ WA ⊓ Wt
  have hxWA : x ∈ WA := by
    -- Proof comment: every coefficient neighborhood contains `x`, so their finite intersection
    -- does as well.
    change x ∈ iInf WA
    intro i
    change x ∈ iInf (UA i)
    intro j
    exact hxUA i j
  have hxWt : x ∈ Wt := by
    -- Proof comment: likewise for the finitely many generator neighborhoods.
    change x ∈ iInf Ut
    intro j
    exact hxUt j
  have hxW : x ∈ W := by
    exact ⟨hx, hxWA, hxWt⟩
  have hWU : W ≤ U := by
    exact inf_le_left
  have hWUA : ∀ i : Fin n, ∀ j : Fin m, W ≤ UA i j := by
    intro i j
    exact le_trans inf_le_right <|
      le_trans inf_le_left <|
        le_trans (iInf_le WA i) (iInf_le (UA i) j)
  have hWUt : ∀ j : Fin m, W ≤ Ut j := by
    intro j
    exact le_trans inf_le_right <|
      le_trans inf_le_right <|
        iInf_le Ut j
  let A_W : Fin n → Fin m → X.presheaf.obj (op W) := fun i j ↦
    X.presheaf.map (homOfLE (hWUA i j)).op (a i j)
  let t_W : Fin m → ℱ.val.obj (op W) := fun j ↦
    ℱ.val.map (homOfLE (hWUt j)).op (tU j)
  refine ⟨W, hxW, hWU, A_W, t_W, ?_, ?_⟩
  · intro i j
    -- Proof comment: restricting a chosen representative to the common refinement preserves its
    -- germ at `x`.
    rw [show A_W i j = X.presheaf.map (homOfLE (hWUA i j)).op (a i j) by rfl]
    rw [TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (hWUA i j)) x hxW (a i j)]
    exact ha i j
  · intro j
    -- Proof comment: the same restriction argument applies to the chosen generator
    -- representatives.
    rw [show t_W j = ℱ.val.map (homOfLE (hWUt j)).op (tU j) by rfl]
    rw [TopCat.Presheaf.germ_res_apply ℱ.val.presheaf (homOfLE (hWUt j)) x hxW (tU j)]
    exact ht j

/-- Helper for Lemma 17.17.11: stalk matrix identities can be made into honest section identities
after shrinking to one common neighborhood of `x`. -/
private theorem existsShrunkOpenWithMatrixRelations
    {U : Opens X} {n m : ℕ}
    (f : Fin n → X.presheaf.obj (op U))
    (s : Fin n → ℱ.val.obj (op U))
    (x : X) (hx : x ∈ U)
    (A : Fin n → Fin m → X.presheaf.stalk x)
    (t : Fin m → RingedSpace.stalkModuleCat ℱ x)
    (hs : ∀ i,
      TopCat.Presheaf.germ ℱ.val.presheaf U x hx (s i) = ∑ j, A i j • t j)
    (hA : ∀ j, ∑ i, TopCat.Presheaf.germ X.presheaf U x hx (f i) * A i j = 0) :
    ∃ (W : Opens X) (_ : x ∈ W) (hWU : W ≤ U)
      (A_W : Fin n → Fin m → X.presheaf.obj (op W))
      (t_W : Fin m → ℱ.val.obj (op W)),
        (∀ i, ℱ.val.map (homOfLE hWU).op (s i) = ∑ j, A_W i j • t_W j) ∧
          ∀ j, ∑ i, X.presheaf.map (homOfLE hWU).op (f i) * A_W i j = 0 := by
  classical
  rcases existsCommonOpenWithStalkRepresentatives
      (X := X) (ℱ := ℱ) f s x hx A t with
    ⟨W, hxW, hWU, A_W, t_W, hA_W, ht_W⟩
  let rowError : Fin n → ℱ.val.obj (op W) := fun i ↦
    ℱ.val.map (homOfLE hWU).op (s i) - ∑ j, A_W i j • t_W j
  let colError : Fin m → X.presheaf.obj (op W) := fun j ↦
    ∑ i, X.presheaf.map (homOfLE hWU).op (f i) * A_W i j
  have rowError_germ_zero :
      ∀ i, TopCat.Presheaf.germ ℱ.val.presheaf W x hxW (rowError i) = 0 := by
    intro i
    let g := stalkGermLinear (X := X) (ℱ := ℱ) x W hxW
    have hs_res :
        g (ℱ.val.map (homOfLE hWU).op (s i)) =
          TopCat.Presheaf.germ ℱ.val.presheaf U x hx (s i) := by
      simpa [g, stalkGermLinear] using
        (TopCat.Presheaf.germ_res_apply ℱ.val.presheaf (homOfLE hWU) x hxW (s i))
    have hsum :
        g (∑ j, A_W i j • t_W j) = ∑ j, A i j • t j := by
      calc
        g (∑ j, A_W i j • t_W j) = ∑ j, g (A_W i j • t_W j) := by
          rw [map_sum]
        _ = ∑ j, A i j • t j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simpa [g, stalkGermLinear, hA_W i j, ht_W j] using
            ((g.map_smulₛₗ (A_W i j) (t_W j)).symm)
    -- Proof comment: after replacing the chosen representatives by their prescribed germs, the
    -- row error has the same germ as the zero stalk relation coming from `hs`.
    change g (rowError i) = 0
    calc
      g (rowError i) = g (ℱ.val.map (homOfLE hWU).op (s i)) - g (∑ j, A_W i j • t_W j) := by
        simp [rowError]
      _ = TopCat.Presheaf.germ ℱ.val.presheaf U x hx (s i) - ∑ j, A i j • t j := by
        rw [hs_res, hsum]
      _ = 0 := by
        rw [hs i]
        simp
  have colError_germ_zero :
      ∀ j, TopCat.Presheaf.germ X.presheaf W x hxW (colError j) = 0 := by
    intro j
    -- Proof comment: the column error is a section whose germ is exactly the stalk relation `hA`.
    calc
      TopCat.Presheaf.germ X.presheaf W x hxW (colError j) =
          ∑ i, TopCat.Presheaf.germ X.presheaf W x hxW
            (X.presheaf.map (homOfLE hWU).op (f i) * A_W i j) := by
              simp [colError, map_sum]
      _ = ∑ i, TopCat.Presheaf.germ X.presheaf U x hx (f i) * A i j := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [map_mul]
            rw [TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hWU) x hxW (f i), hA_W i j]
      _ = 0 := hA j
  have rowZeroNear :
      ∀ i, ∃ (W_i : Opens X) (_ : x ∈ W_i) (_ : W_i ≤ W),
        ℱ.val.map (homOfLE ‹W_i ≤ W›).op (rowError i) = 0 := by
    intro i
    obtain ⟨W_i, hxWi, i₁, i₂, hsec⟩ :=
      TopCat.Presheaf.germ_eq ℱ.val.presheaf x hxW hxW (rowError i) 0 (rowError_germ_zero i)
    let hWiW : W_i ≤ W := i₁.le
    have hi : i₁ = i₂ := by
      apply Subsingleton.elim
    subst hi
    refine ⟨W_i, hxWi, hWiW, ?_⟩
    simpa using hsec
  have colZeroNear :
      ∀ j, ∃ (W_j : Opens X) (_ : x ∈ W_j) (_ : W_j ≤ W),
        X.presheaf.map (homOfLE ‹W_j ≤ W›).op (colError j) = 0 := by
    intro j
    obtain ⟨W_j, hxWj, i₁, i₂, hsec⟩ :=
      TopCat.Presheaf.germ_eq X.presheaf x hxW hxW (colError j) 0 (colError_germ_zero j)
    let hWjW : W_j ≤ W := i₁.le
    have hi : i₁ = i₂ := by
      apply Subsingleton.elim
    subst hi
    refine ⟨W_j, hxWj, hWjW, ?_⟩
    simpa using hsec
  choose W_row hxW_row hW_row hrowzero using rowZeroNear
  choose W_col hxW_col hW_col hcolzero using colZeroNear
  let W_row_inf : Opens X := Finset.univ.inf W_row
  let W_col_inf : Opens X := Finset.univ.inf W_col
  let V : Opens X := W ⊓ W_row_inf ⊓ W_col_inf
  have hxW_row_inf : x ∈ W_row_inf := by
    simp [W_row_inf, hxW_row]
  have hxW_col_inf : x ∈ W_col_inf := by
    simp [W_col_inf, hxW_col]
  have hxV : x ∈ V := by
    exact ⟨hxW, hxW_row_inf, hxW_col_inf⟩
  have hVW : V ≤ W := by
    exact inf_le_left
  have hVW_row_inf : V ≤ W_row_inf := by
    exact le_trans inf_le_right inf_le_left
  have hVW_col_inf : V ≤ W_col_inf := by
    exact le_trans inf_le_right inf_le_right
  have hVW_row : ∀ i : Fin n, V ≤ W_row i := by
    intro i
    exact le_trans hVW_row_inf (Finset.inf_le (by simp))
  have hVW_col : ∀ j : Fin m, V ≤ W_col j := by
    intro j
    exact le_trans hVW_col_inf (Finset.inf_le (by simp))
  let hVU' : V ≤ U := le_trans hVW hWU
  let A_V : Fin n → Fin m → X.presheaf.obj (op V) := fun i j ↦
    X.presheaf.map (homOfLE hVW).op (A_W i j)
  let t_V : Fin m → ℱ.val.obj (op V) := fun j ↦
    ℱ.val.map (homOfLE hVW).op (t_W j)
  refine ⟨V, hxV, hVU', A_V, t_V, ?_, ?_⟩
  · intro i
    have hrowV :
        ℱ.val.map (homOfLE hVW).op (rowError i) = 0 := by
      have hrestrict :=
        congrArg (ℱ.val.map (homOfLE (hVW_row i)).op) (hrowzero i)
      have hcompOp :
          (homOfLE (hW_row i)).op ≫ (homOfLE (hVW_row i)).op = (homOfLE hVW).op := by
        apply Subsingleton.elim
      simpa [FunctorToTypes.map_comp_apply, hcompOp] using hrestrict
    have hrowEq :
        ℱ.val.map (homOfLE hVU').op (s i) - ∑ j, A_V i j • t_V j = 0 := by
      -- Proof comment: restrict the row-error vanishing from its individual neighborhood to the
      -- common intersection and rewrite both sides via functoriality of restriction.
      change ℱ.val.map (homOfLE hVW).op
          (ℱ.val.map (homOfLE hWU).op (s i) - ∑ j, A_W i j • t_W j) = 0 at hrowV
      rw [map_sub, map_sum] at hrowV
      simp_rw [map_smul] at hrowV
      have hcompOp :
          (homOfLE hWU).op ≫ (homOfLE hVW).op = (homOfLE hVU').op := by
        apply Subsingleton.elim
      simpa [A_V, t_V, FunctorToTypes.map_comp_apply, hcompOp] using hrowV
    exact sub_eq_zero.mp hrowEq
  · intro j
    have hcolV :
        X.presheaf.map (homOfLE hVW).op (colError j) = 0 := by
      have hrestrict :=
        congrArg (X.presheaf.map (homOfLE (hVW_col j)).op) (hcolzero j)
      have hcompOp :
          (homOfLE (hW_col j)).op ≫ (homOfLE (hVW_col j)).op = (homOfLE hVW).op := by
        apply Subsingleton.elim
      simpa [FunctorToTypes.map_comp_apply, hcompOp] using hrestrict
    -- Proof comment: the common shrink preserves the column annihilation relation after
    -- re-expressing all coefficients by restriction from `W`.
    change X.presheaf.map (homOfLE hVW).op
        (∑ i, X.presheaf.map (homOfLE hWU).op (f i) * A_W i j) = 0 at hcolV
    rw [map_sum] at hcolV
    simp_rw [map_mul] at hcolV
    have hcompOp :
        (homOfLE hWU).op ≫ (homOfLE hVW).op = (homOfLE hVU').op := by
      apply Subsingleton.elim
    simpa [A_V, FunctorToTypes.map_comp_apply, hcompOp] using hcolV

-- Proof sketch: let `I ⊂ \mathcal O_U` be the image of the map
-- `\mathcal O_U \to \mathcal O_U^{\oplus n}`. The relation `\alpha ≫ \beta = 0` says exactly that
-- the induced map `I ⊗_{\mathcal O_U} \mathcal F|_U \to \mathcal F|_U` kills the corresponding
-- finite family of generators. Flatness of `\mathcal F_x` over `\mathcal O_{X, x}` lets one
-- shrink around `x` so that this tensor relation already vanishes on some neighbourhood `V`. Since
-- the source is finite free, this vanishing can be rewritten as a factorization of the restricted
-- map `\beta|_V` through another finite free module with zero composite from `\alpha|_V`.
/-- Lemma 17.17.11: if a two-step complex
`\mathcal O_U \xrightarrow{\alpha} \mathcal O_U^{\oplus n} \xrightarrow{\beta} \mathcal F|_U`
has stalkwise flat target at `x`, then near `x` the restricted map `\beta` factors through a
finite free module in such a way that the restricted `\alpha` maps to zero. -/
@[stacks 08BK]
theorem exists_local_finite_free_factorization_of_complex_of_flat
    {U : Opens X} {I : Type u} [Finite I]
    (α : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      (SheafOfModules.free.{u} I : SheafOfModules _))
    (β : (SheafOfModules.free.{u} I : SheafOfModules _) ⟶ ℱ.over U)
    (hcomplex : α ≫ β = 0)
    (x : X) (hx : x ∈ U) (hflat : ℱ.flat_at x) :
    ∃ (V : Over U) (_ : x ∈ V.left),
      ∃ (J : Type u) (_ : Finite J)
        (A : ((SheafOfModules.free.{u} I : SheafOfModules (X.ringCatSheaf.over U)).over V) ⟶
          (SheafOfModules.free.{u} J : SheafOfModules ((X.ringCatSheaf.over U).over V)))
        (γ : (SheafOfModules.free.{u} J : SheafOfModules ((X.ringCatSheaf.over U).over V)) ⟶
          (ℱ.over U).over V),
          (α |_ V) ≫ A = 0 ∧
            A ≫ γ = β |_ V := by
  -- Route correction: the source-faithful ideal/tensor proof is not the right Lean surface here.
  -- The verified prefix now normalizes the complex relation to the stalk and extracts finite stalk
  -- matrix data via `existsStalkFactorizationDataOfComplexOfFlat`.
  -- TODO: `existsCommonOpenWithStalkRepresentatives` now lifts all finitely many stalk
  -- coefficients and generators to one neighborhood. The remaining blocker is to shrink once more
  -- with `TopCat.Presheaf.germ_eq` so the row and column relations hold on a single neighborhood,
  -- and then package those local families into the morphisms `A` and `γ` through
  -- `overRestrictionFreeIso`.
  sorry

-- Proof sketch: apply the owner theorem to the morphisms corresponding under
-- `SheafOfModules.freeHomEquiv` to the families `(f_i)` and `(s_i)`. Unwinding those morphisms on
-- a shrunken neighbourhood gives the matrix coefficients `a_{ij}` and local sections `t_j`.
/-- Source-facing matrix form of Lemma 17.17.11: if families `f_i` and `s_i` define a complex
`\mathcal O_U \to \mathcal O_U^{\oplus n} \to \mathcal F|_U` with `\mathcal F_x` flat, then near
`x` the restricted family `s_i` factors through finitely many local sections `t_j` with matrix
coefficients annihilating the restricted `f_i`. -/
@[stacks 08BK]
theorem exists_local_matrix_factorization_of_complex_of_flat
    {U : Opens X} {n : ℕ}
    (f : Fin n → X.presheaf.obj (op U))
    (s : Fin n → ℱ.val.obj (op U))
    (hcomplex : ∑ i, f i • s i = 0)
    (x : X) (hx : x ∈ U) (hflat : ℱ.flat_at x) :
    ∃ (V : Opens X) (_ : x ∈ V) (hVU : V ≤ U) (m : ℕ)
      (A : Fin n → Fin m → X.presheaf.obj (op V))
      (t : Fin m → ℱ.val.obj (op V)),
        (∀ i, ℱ.val.map (homOfLE hVU).op (s i) = ∑ j, A i j • t j) ∧
          ∀ j, ∑ i, X.presheaf.map (homOfLE hVU).op (f i) * A i j = 0 := by
  rcases existsStalkFactorizationDataOfComplexOfFlat
      (X := X) (ℱ := ℱ) f s hcomplex x hx hflat with
    ⟨m, A, t, hs, hA⟩
  -- Proof comment: first produce finite stalk matrix data from flatness, then shrink once more so
  -- those stalk equalities become honest section equalities on one neighborhood.
  rcases existsShrunkOpenWithMatrixRelations
      (X := X) (ℱ := ℱ) f s x hx A t hs hA with
    ⟨V, hxV, hVU, A_V, t_V, hsV, hAV⟩
  exact ⟨V, hxV, hVU, m, A_V, t_V, hsV, hAV⟩

end AlgebraicGeometry.RingedSpace
