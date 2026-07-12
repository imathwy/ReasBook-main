import Mathlib
import StacksProject_2024.Chap15.Remark_15_88_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Pretriangulated
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "SeqMod" => SequentialInverseSystem (ModuleCat A)
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "DSeq" => DerivedCategory SeqMod
local notation "KSeq" => HomotopyCategory SeqMod (ComplexShape.up ℤ)
local notation "CpxSeq" => CochainComplex SeqMod ℤ
local notation "Δ" => (Functor.const ℕᵒᵖ : ModuleCat A ⥤ SeqMod)

/- Domain-style sampling for Lemma 15.88.11:
- primary domain: exactness of the fixed-left-factor functor
  `E ↦ R lim (E ⊗_A^{\mathbf L} Δ(K))` on `D(ℕᵒᵖ ⥤ Mod A)`;
- sampled owner declarations:
  `Functor.mapDerivedCategory`,
  `additiveFunctorTotalRightDerived`,
  `Functor.IsTriangulated`,
  `Functor.map_distinguished`;
- best owner abstraction: the source-facing owner remains the composite functor
  `derivedInverseLimitTensorOnInverseSystemFunctor K`, while exactness is controlled canonically
  by `Functor.IsTriangulated`; the fixed-base derived inverse-limit factor should therefore be
  reused directly from `Lemma_15_88_1_FixedBase` rather than wrapped in a second local owner;
- primitive vs. derived:
  primitive data are the fixed object `K : D(A)` and the private derived left-tensor bridge on
  `D(ℕᵒᵖ ⥤ Mod A)`;
  derived API is the source-facing composite functor, its canonical `Functor.IsTriangulated`
  exactness theorem, and the mapped distinguished-triangle corollary;
- source/core/bridge triage:
  `source-facing`: `derivedInverseLimitTensorOnInverseSystemFunctor`, its owner-level exactness
    theorem, and the mapped-triangle corollary below;
  `core/canonical`: `Δ.mapDerivedCategory`,
    `additiveFunctorTotalRightDerived (lim : SeqMod ⥤ ModuleCat A)`,
    `Functor.IsTriangulated`, and `Functor.map_distinguished`;
  `bridge/view`: the private fixed-left-factor derived tensor helper used to express the source
    functor without introducing a second public tensor owner. -/

/-- The pointwise tensor product on sequential inverse systems of `A`-modules is additive in each
variable. -/
local instance sequentialAModuleInverseSystem_monoidalPreadditive_left :
    MonoidalPreadditive SeqMod where
  whiskerLeft_zero := by
    intro X Y Z
    apply NatTrans.ext
    funext n
    change X.obj n ◁ (0 : Y.obj n ⟶ Z.obj n) = 0
    simp
  zero_whiskerRight := by
    intro X Y Z
    apply NatTrans.ext
    funext n
    change (0 : Y.obj n ⟶ Z.obj n) ▷ X.obj n = 0
    simp
  whiskerLeft_add := by
    intro X Y Z f g
    apply NatTrans.ext
    funext n
    change X.obj n ◁ (f.app n + g.app n) = X.obj n ◁ f.app n + X.obj n ◁ g.app n
    simp
  add_whiskerRight := by
    intro X Y Z f g
    apply NatTrans.ext
    funext n
    change (f.app n + g.app n) ▷ X.obj n = f.app n ▷ X.obj n + g.app n ▷ X.obj n
    simp

/-- The constant inverse-system functor on `A`-modules is additive. -/
local instance constantSequentialAModuleFunctor_additive :
    (Δ : ModuleCat A ⥤ SeqMod).Additive where
  -- Additivity is checked stagewise on the constant inverse system.
  map_add := by
    intro X Y f g
    ext n x
    rfl

/-- The homotopy-category tensor-totalization functor on sequential inverse systems with fixed
left tensor factor. -/
private abbrev totalizedTensorWithFixedComplexHomotopyFunctor
    (P : CpxSeq) :
    KSeq ⥤ KSeq :=
  CategoryTheory.Quotient.lift _
    ((((curriedTensor SeqMod).map₂CochainComplex).obj P) ⋙
      HomotopyCategory.quotient SeqMod (up ℤ))
    (fun _ _ _ _ ⟨h⟩ ↦
      HomotopyCategory.eq_of_homotopy _ _
        (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 P) h
          (curriedTensor SeqMod) (up ℤ)))

/-- The homotopy-category source functor whose total left derived functor computes tensoring on
the left by a chosen derived inverse system. -/
private abbrev tensorLeftDerivedSourceFunctor
    (K : DMod) : KSeq ⥤ DSeq :=
  totalizedTensorWithFixedComplexHomotopyFunctor
      (((DerivedCategory.Qh : KSeq ⥤ DSeq).objPreimage
        ((((Δ : ModuleCat A ⥤ SeqMod).mapDerivedCategory) : DMod ⥤ DSeq).obj K)).as) ⋙
    (DerivedCategory.Qh : KSeq ⥤ DSeq)

/-- Tensoring on the left with a fixed derived inverse system admits a total left derived
endofunctor on `D(ℕᵒᵖ ⥤ Mod A)`. -/
private theorem tensorLeftDerivedSourceFunctor_hasLeftDerivedFunctor
    (K : DMod) :
    (tensorLeftDerivedSourceFunctor K).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso SeqMod (up ℤ)) := by
  -- TODO: follow the fixed-left-factor analogue of `Remark_15_88_10` by comparing the chosen
  -- diagonal representative of `K` with a K-flat model and applying quasi-isomorphism invariance
  -- of tensoring on the left. This is the only remaining structural input.
  sorry

/-- The fixed-left-factor derived tensor endofunctor on `D(ℕᵒᵖ ⥤ Mod A)`. This helper stays
private so the lemma exposes only the source-facing composite functor below. -/
private noncomputable abbrev tensorLeftDerivedFunctor
    (K : DMod) : DSeq ⥤ DSeq :=
  letI := tensorLeftDerivedSourceFunctor_hasLeftDerivedFunctor K
  (tensorLeftDerivedSourceFunctor K).totalLeftDerived
    (DerivedCategory.Qh : KSeq ⥤ DSeq)
    (HomotopyCategory.quasiIso SeqMod (up ℤ))

/-- The private fixed-left-factor derived tensor helper admits a shift-commuting structure. -/
private theorem tensorLeftDerivedFunctor_commShift_exists
    (K : DMod) :
    Nonempty ((tensorLeftDerivedFunctor K).CommShift ℤ) := by
  -- TODO: once the left-derived existence theorem above is available with the canonical
  -- shift-commuting comparison, instantiate the standard `CommShift` structure on the total left
  -- derived functor exactly as in `Definition_21_17_13`.
  sorry

/-- A private shift-commuting witness for the fixed-left-factor derived tensor helper, used only
to form the mapped distinguished triangle below. -/
private noncomputable instance tensorLeftDerivedFunctor_commShift
    (K : DMod) :
    (tensorLeftDerivedFunctor K).CommShift ℤ :=
  Classical.choice (tensorLeftDerivedFunctor_commShift_exists K)

/-- For a fixed `K ∈ D(A)`, this is the exact functor
`E ↦ R lim (E ⊗_A^{\mathbf L} Δ(K))` on `D(ℕᵒᵖ ⥤ Mod A)`, canonically identifying with the
textbook construction `E ↦ R lim (Δ(K) ⊗_A^{\mathbf L} E)` from Remark `15.88.10` by symmetry of
the derived tensor product. -/
abbrev derivedInverseLimitTensorOnInverseSystemFunctor
    (K : DMod) : DSeq ⥤ DMod :=
  tensorLeftDerivedFunctor K ⋙
    additiveFunctorTotalRightDerived.{u + 1, u + 1, u + 1, u, u}
      (lim : SeqMod ⥤ ModuleCat A)

/-- A private shift-commuting witness for the source-facing tensor-derived-inverse-limit functor,
used only to state its mapped-triangle output canonically. -/
private noncomputable instance derivedInverseLimitTensorOnInverseSystemFunctor_commShift
    (K : DMod) :
    (derivedInverseLimitTensorOnInverseSystemFunctor K).CommShift ℤ := by
  letI : (tensorLeftDerivedFunctor K).CommShift ℤ :=
    tensorLeftDerivedFunctor_commShift K
  dsimp [derivedInverseLimitTensorOnInverseSystemFunctor]
  infer_instance

/-- Helper for Lemma 15.88.11: tensoring on the left by the diagonal image of `K` is exact on
`D(\mathbf N^\mathrm{op} \to \mathrm{Mod}_A)`. -/
private theorem tensorLeftDerivedFunctor_isTriangulated
    (K : DMod) :
    (tensorLeftDerivedFunctor K).IsTriangulated := by
  -- TODO: after constructing the fixed-left total left derived functor compatibly with shift,
  -- apply the canonical `IsTriangulated` instance for total left derived functors, again following
  -- the `Definition_21_17_13` pattern.
  sorry

-- Proof sketch: the constant-system functor sends `K` to the diagonal inverse system `Δ(K)`,
-- and the derived tensor product is exact in each variable; composing with the fixed-base
-- derived inverse-limit functor therefore sends distinguished triangles in
-- `D(ℕᵒᵖ ⥤ Mod A)` to distinguished triangles in `D(A)`.
/-- The functor `E ↦ R lim (Δ(K) ⊗_A^{\mathbf L} E)` is exact in the triangulated sense. -/
theorem derivedInverseLimitTensorOnInverseSystemFunctor_isTriangulated
    (K : DMod) :
    (derivedInverseLimitTensorOnInverseSystemFunctor K).IsTriangulated := by
  -- TODO: combine the exactness of the fixed-left derived tensor helper with the exactness of the
  -- fixed-base derived inverse-limit functor, using the standard composition proof pattern from
  -- `Lemma_15_60_1`.
  sorry

/-- Lemma 15.88.11: if `T` is a distinguished triangle in `D(\mathbf N, A)`, then for every
`K ∈ D(A)` the canonical triangle obtained by applying
`E ↦ R \!\varprojlim (\Delta(K) \otimes_A^{\mathbf L} E)` is distinguished in `D(A)`. In the
notation of the text, for `T = (E ⟶ D ⟶ F ⟶ E[1])` this is the canonical distinguished triangle
`R \!\varprojlim (K \otimes_A^{\mathbf L} E_n) ⟶
R \!\varprojlim (K \otimes_A^{\mathbf L} D_n) ⟶
R \!\varprojlim (K \otimes_A^{\mathbf L} F_n) ⟶
R \!\varprojlim (K \otimes_A^{\mathbf L} E_n)[1]` from Remark `15.88.10`. -/
@[stacks 091K]
theorem derivedInverseLimitTensorOnInverseSystemFunctor_map_distinguished
    (K : DMod) (T : Triangle DSeq) (hT : T ∈ distTriang DSeq) :
    ((derivedInverseLimitTensorOnInverseSystemFunctor K).mapTriangle.obj T) ∈ distTriang DMod :=
  by
    letI : (derivedInverseLimitTensorOnInverseSystemFunctor K).IsTriangulated :=
      derivedInverseLimitTensorOnInverseSystemFunctor_isTriangulated K
    simpa using (derivedInverseLimitTensorOnInverseSystemFunctor K).map_distinguished T hT

end
