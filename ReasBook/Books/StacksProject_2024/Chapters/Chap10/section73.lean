import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_73_1 (from Chap10) -/
noncomputable section

open CategoryTheory Limits Abelian

universe u

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable (M : ModuleCat.{u} R) (N' : ModuleCat.{u} R')

attribute [local instance] HasDerivedCategory.standard

private abbrev extScalars :=
  ModuleCat.extendScalars (algebraMap R R')

private abbrev resScalars :=
  ModuleCat.restrictScalars (algebraMap R R')

private abbrev baseChangeAdj :=
  ModuleCat.extendRestrictScalarsAdj (algebraMap R R')

/-
Domain triage:
- `source-facing`: `moduleCatExtFlatBaseChangeComparison` is the textbook flat base-change map on
  `Ext`.
- `core/canonical`: the owner abstractions are `Functor.mapExtAddHom` for `extScalars` and
  `resScalars`, together with the unit/counit of `ModuleCat.extendRestrictScalarsAdj`.
- `bridge/view`: `moduleCatExtFlatBaseChangeAdjointComparison` is the adjoint transpose of the
  source-facing map, expressed directly from the owner API rather than from a parallel wrapper.

Primitive data are only the ring map and the two modules. The comparison maps are derived from the
change-of-rings adjunction and `Ext` functoriality, so no extra packaged data is introduced.
-/

/- The textbook base-change comparison
`Ext^i_{R'}(R' ⊗[R] M, N') → Ext^i_R(M, N'|_R)`, which is the canonical owner-object form of the
source-facing textbook map `Ext^i_{R'}(M ⊗[R] R', N') → Ext^i_R(M, N'|_R)` via tensor symmetry. -/
def moduleCatExtFlatBaseChangeComparison (i : ℕ) :
    Ext (extScalars.obj M) N' i →+ Ext M (resScalars.obj N') i :=
  AddMonoidHom.comp
    ((Ext.mk₀ (baseChangeAdj.unit.app M)).precomp (resScalars.obj N') (zero_add i))
    (resScalars.mapExtAddHom (extScalars.obj M) N' i)

/-- The adjoint-transposed comparison from `Ext_R(M, N'|_R)` to
`Ext_{R'}(R' ⊗[R] M, N')`, obtained by applying `Ext` to extension of scalars and then
postcomposing with the adjunction counit. This is a `bridge/view` companion to the source-facing
map of Lemma `10.73.1`. -/
abbrev moduleCatExtFlatBaseChangeAdjointComparison
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    Ext M (resScalars.obj N') i →+ Ext (extScalars.obj M) N' i :=
  let adj := ModuleCat.extendRestrictScalarsAdj (algebraMap R R')
  letI : PreservesFiniteLimits extScalars :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  letI : extScalars.Additive := adj.left_adjoint_additive
  AddMonoidHom.comp
    ((Ext.mk₀ (adj.counit.app N')).postcomp (extScalars.obj M) (add_zero i))
    (extScalars.mapExtAddHom M (resScalars.obj N') i)

/-- Helper for Lemma 10.73.1: the source-facing comparison sends an `Ext` class to the class
obtained by restricting scalars and precomposing with the adjunction unit. -/
private lemma moduleCatExtFlatBaseChangeComparison_apply (i : ℕ)
    (x : Ext (extScalars.obj M) N' i) :
    moduleCatExtFlatBaseChangeComparison M N' i x =
      (Ext.mk₀ (baseChangeAdj.unit.app M)).comp (x.mapExactFunctor resScalars) (zero_add i) := by
  rfl

/-- Helper for Lemma 10.73.1: the adjoint-transposed comparison sends an `Ext` class to the class
obtained by extending scalars and postcomposing with the adjunction counit. -/
private lemma moduleCatExtFlatBaseChangeAdjointComparison_apply
    (hf : (algebraMap R R').Flat)
    [PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R R'))]
    [(ModuleCat.extendScalars (algebraMap R R')).Additive]
    (i : ℕ) (x : Ext M (resScalars.obj N') i) :
    moduleCatExtFlatBaseChangeAdjointComparison M N' hf i x =
      (x.mapExactFunctor (ModuleCat.extendScalars (algebraMap R R'))).comp
        (Ext.mk₀ ((baseChangeAdj).counit.app N')) (add_zero i) := by
  rfl

/-- Helper for Lemma 10.73.1: on the shifted-Hom representative, the source-facing comparison
followed by its adjoint transpose acts by the identity. -/
private lemma moduleCatExtFlatBaseChange_left_roundtrip_transport
    (hf : (algebraMap R R').Flat) (i : ℕ) (x : Ext (extScalars.obj M) N' i) :
    ((moduleCatExtFlatBaseChangeAdjointComparison M N' hf i)
        ((moduleCatExtFlatBaseChangeComparison M N' i) x)).hom =
      x.hom := by
  -- Route correction: rewrite the whole left roundtrip on `x.hom` once, so the remaining core is
  -- exactly the adjunction `homEquiv` followed by `homEquiv.symm`.
  let adj := baseChangeAdj (R := R) (R' := R')
  letI : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R R')) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  letI : (ModuleCat.extendScalars (algebraMap R R')).Additive := adj.left_adjoint_additive
  letI := HasDerivedCategory.standard (ModuleCat R')
  rw [moduleCatExtFlatBaseChangeAdjointComparison_apply (M := M) (N' := N') hf,
    moduleCatExtFlatBaseChangeComparison_apply (M := M) (N' := N')]
  -- Move the outer `Ext.comp` to shifted-Hom level before simplifying the transport data.
  calc
    ((Ext.mapExactFunctor (ModuleCat.extendScalars (algebraMap R R'))
          ((Ext.mk₀ (baseChangeAdj.unit.app M)).comp (Ext.mapExactFunctor resScalars x)
            (zero_add i))).comp
        (Ext.mk₀ (baseChangeAdj.counit.app N'))
        (add_zero i)).hom
      = (Ext.mapExactFunctor (ModuleCat.extendScalars (algebraMap R R'))
            ((Ext.mk₀ (baseChangeAdj.unit.app M)).comp (Ext.mapExactFunctor resScalars x)
              (zero_add i))).hom.comp
          (Ext.mk₀ (baseChangeAdj.counit.app N')).hom
          (by simp) := by
            simpa using
              (Ext.comp_hom
                (α := Ext.mapExactFunctor (ModuleCat.extendScalars (algebraMap R R'))
                  ((Ext.mk₀ (baseChangeAdj.unit.app M)).comp (Ext.mapExactFunctor resScalars x)
                    (zero_add i)))
                (β := Ext.mk₀ (baseChangeAdj.counit.app N'))
                (h := add_zero i))
    _ = x.hom := by
      simp only [Abelian.Ext.mapExactFunctor_hom, Ext.comp_hom, Ext.mk₀_hom,
        ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, Functor.map_comp, Functor.map_id,
        Category.assoc,
        Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc,
        Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app,
        Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_inv_app]
      -- TODO: the normalized goal is now a single `ShiftedHom.comp` built from the transported
      -- unit morphism and the mapped `x.hom`, followed by `ShiftedHom.mk₀` of the counit.
      -- The next source-faithful step is to use `ShiftedHom.comp_mk₀` and
      -- `ShiftedHom.map_naturality` to identify this with the adjunction roundtrip
      -- `homEquiv.symm (homEquiv x.hom)`.
      sorry

/-- Helper for Lemma 10.73.1: on the shifted-Hom representative, the source-facing comparison
followed by its adjoint transpose acts by the identity. -/
private lemma moduleCatExtFlatBaseChange_leftInverse_hom
    (hf : (algebraMap R R').Flat) (i : ℕ) (x : Ext (extScalars.obj M) N' i) :
    ((moduleCatExtFlatBaseChangeAdjointComparison M N' hf i)
        ((moduleCatExtFlatBaseChangeComparison M N' i) x)).hom =
      x.hom := by
  -- Reduce the left inverse to the cached whole-composite normalization.
  letI := HasDerivedCategory.standard (ModuleCat R')
  simpa using moduleCatExtFlatBaseChange_left_roundtrip_transport
    (M := M) (N' := N') hf i x

/-- Helper for Lemma 10.73.1: the hom-level left inverse identity upgrades to an equality of
`Ext` classes. -/
private lemma moduleCatExtFlatBaseChange_leftInverse_pointwise
    (hf : (algebraMap R R').Flat) (i : ℕ) (x : Ext (extScalars.obj M) N' i) :
    (moduleCatExtFlatBaseChangeAdjointComparison M N' hf i)
        ((moduleCatExtFlatBaseChangeComparison M N' i) x) =
      x := by
  -- Repackage the shifted-Hom identity as an equality in `Ext`.
  letI := HasDerivedCategory.standard (ModuleCat R')
  rw [Ext.ext_iff]
  exact moduleCatExtFlatBaseChange_leftInverse_hom (M := M) (N' := N') hf i x

/-- Helper for Lemma 10.73.1: on the shifted-Hom representative, the adjoint transpose followed by
the source-facing comparison acts by the identity. -/
private lemma moduleCatExtFlatBaseChange_right_roundtrip_transport
    (hf : (algebraMap R R').Flat) (i : ℕ) (x : Ext M (resScalars.obj N') i) :
    ((moduleCatExtFlatBaseChangeComparison M N' i)
        ((moduleCatExtFlatBaseChangeAdjointComparison M N' hf i) x)).hom =
      x.hom := by
  -- Route correction: rewrite the whole right roundtrip on `x.hom` once, so the remaining core is
  -- exactly the adjunction `homEquiv.symm` followed by `homEquiv`.
  let adj := baseChangeAdj (R := R) (R' := R')
  letI : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R R')) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  letI : (ModuleCat.extendScalars (algebraMap R R')).Additive := adj.left_adjoint_additive
  letI := HasDerivedCategory.standard (ModuleCat R)
  rw [moduleCatExtFlatBaseChangeComparison_apply (M := M) (N' := N'),
    moduleCatExtFlatBaseChangeAdjointComparison_apply (M := M) (N' := N') hf]
  -- Again, move the outer `Ext.comp` to shifted-Hom level before simplifying transport.
  calc
    ((Ext.mk₀ (baseChangeAdj.unit.app M)).comp
        (Ext.mapExactFunctor resScalars
          ((Ext.mapExactFunctor (ModuleCat.extendScalars (algebraMap R R')) x).comp
            (Ext.mk₀ (baseChangeAdj.counit.app N'))
            (add_zero i)))
        (zero_add i)).hom
      = (Ext.mk₀ (baseChangeAdj.unit.app M)).hom.comp
          (Ext.mapExactFunctor resScalars
            ((Ext.mapExactFunctor (ModuleCat.extendScalars (algebraMap R R')) x).comp
              (Ext.mk₀ (baseChangeAdj.counit.app N'))
              (add_zero i))).hom
          (by simp) := by
            simpa using
              (Ext.comp_hom
                (α := Ext.mk₀ (baseChangeAdj.unit.app M))
                (β := Ext.mapExactFunctor resScalars
                  ((Ext.mapExactFunctor (ModuleCat.extendScalars (algebraMap R R')) x).comp
                    (Ext.mk₀ (baseChangeAdj.counit.app N'))
                    (add_zero i)))
                (h := zero_add i))
    _ = x.hom := by
      simp only [Abelian.Ext.mapExactFunctor_hom, Ext.comp_hom, Ext.mk₀_hom,
        ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, Functor.map_comp, Functor.map_id,
        Category.assoc,
        Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc,
        Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app,
        Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_inv_app]
      -- TODO: the normalized goal is now the reverse shifted-Hom transport composite through the
      -- unit on `M`, the transported `x.hom`, and the counit on `N'`.
      -- The next source-faithful step is to rewrite this composite with `ShiftedHom.map_naturality`
      -- and then collapse it to the roundtrip `homEquiv (homEquiv.symm x.hom)`.
      sorry

/-- Helper for Lemma 10.73.1: on the shifted-Hom representative, the adjoint transpose followed by
the source-facing comparison acts by the identity. -/
private lemma moduleCatExtFlatBaseChange_rightInverse_hom
    (hf : (algebraMap R R').Flat) (i : ℕ) (x : Ext M (resScalars.obj N') i) :
    ((moduleCatExtFlatBaseChangeComparison M N' i)
        ((moduleCatExtFlatBaseChangeAdjointComparison M N' hf i) x)).hom =
      x.hom := by
  -- Reduce the right inverse to the cached whole-composite normalization.
  letI := HasDerivedCategory.standard (ModuleCat R)
  simpa using moduleCatExtFlatBaseChange_right_roundtrip_transport
    (M := M) (N' := N') hf i x

/-- Helper for Lemma 10.73.1: the hom-level right inverse identity upgrades to an equality of
`Ext` classes. -/
private lemma moduleCatExtFlatBaseChange_rightInverse_pointwise
    (hf : (algebraMap R R').Flat) (i : ℕ) (x : Ext M (resScalars.obj N') i) :
    (moduleCatExtFlatBaseChangeComparison M N' i)
        ((moduleCatExtFlatBaseChangeAdjointComparison M N' hf i) x) =
      x := by
  -- Repackage the shifted-Hom identity as an equality in `Ext`.
  letI := HasDerivedCategory.standard (ModuleCat R)
  rw [Ext.ext_iff]
  exact moduleCatExtFlatBaseChange_rightInverse_hom (M := M) (N' := N') hf i x

/-- Helper for Lemma 10.73.1: the adjoint-transposed base-change comparison is a left inverse to
the source-facing base-change comparison. -/
private lemma moduleCatExtFlatBaseChange_leftInverse
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    AddMonoidHom.comp
        (moduleCatExtFlatBaseChangeAdjointComparison M N' hf i)
        (moduleCatExtFlatBaseChangeComparison M N' i) =
      AddMonoidHom.id (Ext (extScalars.obj M) N' i) := by
  -- After the pointwise `Ext` identity is proved, the additive-hom equality is extensional.
  rw [AddMonoidHom.ext_iff]
  intro x
  exact moduleCatExtFlatBaseChange_leftInverse_pointwise (M := M) (N' := N') hf i x

/-- Helper for Lemma 10.73.1: the adjoint-transposed base-change comparison is a right inverse to
the source-facing base-change comparison. -/
private lemma moduleCatExtFlatBaseChange_rightInverse
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    AddMonoidHom.comp
        (moduleCatExtFlatBaseChangeComparison M N' i)
        (moduleCatExtFlatBaseChangeAdjointComparison M N' hf i) =
      AddMonoidHom.id (Ext M (resScalars.obj N') i) := by
  -- Again, the additive-hom equality is just the pointwise `Ext` inverse law.
  rw [AddMonoidHom.ext_iff]
  intro x
  exact moduleCatExtFlatBaseChange_rightInverse_pointwise (M := M) (N' := N') hf i x

-- Proof sketch: choose a projective resolution `P• → M`; flatness makes `R' ⊗[R] P•` a
-- projective resolution of `R' ⊗[R] M`, and Lemma `10.14.3` identifies the two Hom complexes
-- `Hom_{R'}(R' ⊗[R] P•, N')` and `Hom_R(P•, N')`, so the induced comparison on homology is
-- bijective in every degree.
/-- Lemma 10.73.1: for a flat ring map `R → R'`, an `R`-module `M`, and an `R'`-module `N'`,
the textbook natural map
`Ext^i_{R'}(M ⊗[R] R', N') → Ext^i_R(M, N'|_R)`
is an isomorphism for every `i`; equivalently, the canonical owner-object comparison
`Ext^i_{R'}(R' ⊗[R] M, N') → Ext^i_R(M, N'|_R)` is an isomorphism. -/
theorem moduleCat_ext_flat_baseChange_isIso
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    IsIso (AddCommGrpCat.ofHom (moduleCatExtFlatBaseChangeComparison M N' i)) := by
  -- The inverse is the adjoint-transposed comparison, and the two compositions are the identity.
  refine ⟨⟨AddCommGrpCat.ofHom (moduleCatExtFlatBaseChangeAdjointComparison M N' hf i), ?_, ?_⟩⟩
  · simpa using congrArg AddCommGrpCat.ofHom
      (moduleCatExtFlatBaseChange_leftInverse (M := M) (N' := N') hf i)
  · simpa using congrArg AddCommGrpCat.ofHom
      (moduleCatExtFlatBaseChange_rightInverse (M := M) (N' := N') hf i)

/-- Companion reformulation of Lemma 10.73.1 as bijectivity of the source-facing textbook map. -/
theorem moduleCat_ext_flat_baseChange_bijective
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    Function.Bijective (moduleCatExtFlatBaseChangeComparison M N' i) := by
  let f := AddCommGrpCat.ofHom (moduleCatExtFlatBaseChangeComparison M N' i)
  letI : IsIso f := moduleCat_ext_flat_baseChange_isIso M N' hf i
  exact ⟨(AddCommGrpCat.mono_iff_injective f).mp inferInstance,
    (AddCommGrpCat.epi_iff_surjective f).mp inferInstance⟩

/-- The adjoint-transposed comparison is likewise an isomorphism under the flatness hypothesis. -/
theorem moduleCat_ext_flat_baseChange_adjoint_isIso
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    IsIso (AddCommGrpCat.ofHom (moduleCatExtFlatBaseChangeAdjointComparison M N' hf i)) := by
  -- Swap the two inverse identities proved above.
  refine ⟨⟨AddCommGrpCat.ofHom (moduleCatExtFlatBaseChangeComparison M N' i), ?_, ?_⟩⟩
  · simpa using congrArg AddCommGrpCat.ofHom
      (moduleCatExtFlatBaseChange_rightInverse (M := M) (N' := N') hf i)
  · simpa using congrArg AddCommGrpCat.ofHom
      (moduleCatExtFlatBaseChange_leftInverse (M := M) (N' := N') hf i)

/-- Companion reformulation of the adjoint-transposed comparison as a bijection. -/
theorem moduleCat_ext_flat_baseChange_adjoint_bijective
    (hf : (algebraMap R R').Flat) (i : ℕ) :
    Function.Bijective (moduleCatExtFlatBaseChangeAdjointComparison M N' hf i) := by
  let f := AddCommGrpCat.ofHom (moduleCatExtFlatBaseChangeAdjointComparison M N' hf i)
  letI : IsIso f := moduleCat_ext_flat_baseChange_adjoint_isIso M N' hf i
  exact ⟨(AddCommGrpCat.mono_iff_injective f).mp inferInstance,
    (AddCommGrpCat.epi_iff_surjective f).mp inferInstance⟩

end
