import Mathlib
import StacksProject_2024.Chap10.Lemma_10_8_8
import StacksProject_2024.Chap10.Lemma_10_39_3
import StacksProject_2024.Chap12.Lemma_12_13_9
import StacksProject_2024.Chap13.Lemma_13_29_1
import StacksProject_2024.Chap15.Definition_15_59_1
import StacksProject_2024.Chap15.Lemma_15_59_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ZeroObject

noncomputable section

universe u

namespace CochainComplex

variable {R : Type u} [CommRing R]

private abbrev FreeObj : CategoryTheory.ObjectProperty (ModuleCat.{u} R) :=
  fun X ↦ Module.Free R X

/-- Helper for Lemma 15.59.10: free `R`-modules are stable under isomorphisms in `ModuleCat R`. -/
local instance freeObj_isClosedUnderIsomorphisms :
    CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms (FreeObj (R := R)) where
  of_iso {X Y} e hX := by
    let _ : Module.Free R X := hX
    exact Module.Free.of_equiv e.toLinearEquiv

/-- Helper for Lemma 15.59.10: the zero `R`-module is free, so `FreeObj` contains zero. -/
local instance freeObj_containsZero :
    CategoryTheory.ObjectProperty.ContainsZero (FreeObj (R := R)) where
  exists_zero := ⟨ModuleCat.of R PUnit,
    (ModuleCat.isZero_iff_subsingleton).2 inferInstance,
    Module.Free.of_subsingleton (R := R) (N := PUnit)⟩

/-- Helper for Lemma 15.59.10: every `R`-module is the quotient of a free `R`-module. -/
local instance freeObj_hasEpiCover :
    CategoryTheory.ObjectProperty.HasEpiCover (FreeObj (R := R)) where
  exists_epi (X : ModuleCat.{u} R) := by
    refine ⟨(ModuleCat.free R).obj (X : Type u), ?_, (ModuleCat.adj R).counit.app X, ?_⟩
    · change Module.Free R ((X : Type u) →₀ R)
      exact Module.Free.of_basis
        (Finsupp.basisSingleOne : Module.Basis (X : Type u) R ((X : Type u) →₀ R))
    · -- The free-forgetful counit sends the canonical generator `freeMk x` to `x`.
      refine (ModuleCat.epi_iff_surjective _).2 ?_
      intro x
      refine ⟨ModuleCat.freeMk x, ?_⟩
      have hCounit :
          (ModuleCat.adj R).counit.app X = ModuleCat.freeDesc (fun y : (X : Type u) ↦ y) := by
        simpa [ModuleCat.adj_homEquiv] using ((ModuleCat.adj R).homEquiv_symm_id X).symm
      simpa [hCounit] using
        (ModuleCat.freeDesc_apply (R := R) (f := fun y : (X : Type u) ↦ y) x)

/-- Helper for Lemma 15.59.10: binary coproducts of free `R`-modules are free. -/
local instance freeObj_isClosedUnderBinaryCoproducts :
    CategoryTheory.ObjectProperty.IsClosedUnderBinaryCoproducts (FreeObj (R := R)) := by
  refine CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro Z ⟨F, hF⟩
  let A := F.obj ⟨WalkingPair.left⟩
  let B := F.obj ⟨WalkingPair.right⟩
  let _ : Module.Free R A := hF ⟨WalkingPair.left⟩
  let _ : Module.Free R B := hF ⟨WalkingPair.right⟩
  have hBiprod : Module.Free R (A ⊞ B : ModuleCat R) := by
    let _ : Module.Free R (ModuleCat.of R (A × B)) := inferInstance
    exact Module.Free.of_equiv (ModuleCat.biprodIsoProd A B).symm.toLinearEquiv
  have hCoprod : Module.Free R (A ⨿ B : ModuleCat R) := by
    exact CategoryTheory.ObjectProperty.prop_of_iso (P := FreeObj (R := R))
      (biprod.isoCoprod A B) hBiprod
  have hPairColimit : Module.Free R (A ⨿ B : ModuleCat R) := hCoprod
  -- Route correction: first reduce the binary diagram to the canonical `pair`, then transport
  -- the chosen coproduct back along `diagramIsoPair`.
  exact CategoryTheory.ObjectProperty.prop_of_iso (P := FreeObj (R := R))
    (HasColimit.isoOfNatIso (diagramIsoPair F)).symm hPairColimit

/-- Helper for Lemma 15.59.10: finite coproducts of free `R`-modules are free. -/
local instance freeObj_isClosedUnderFiniteCoproducts :
    CategoryTheory.ObjectProperty.IsClosedUnderFiniteCoproducts (FreeObj (R := R)) :=
  CategoryTheory.ObjectProperty.IsClosedUnderFiniteCoproducts.mk'

/-
Domain sampling pass:
* primary domain: K-flat resolutions of cochain complexes of `R`-modules;
* sampled owner declarations:
  - `CochainComplex.IsKFlat` and `CochainComplex.IsTermwiseFlat` from
    `Definition_15_59_1`, the chapter owners for the two ambient properties carried by the
    resolving complex;
  - `cochainComplex_epi_iff_degreewise_epi` from `Lemma_12_13_9`, the source-facing bridge
    between the termwise epimorphism condition from the text and the canonical complex-level owner
    `Epi π`;
  - `CategoryTheory.IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn` and
    `CategoryTheory.UpperTruncationResolutionTower` from Chapter 13, the canonical owner
    abstractions for the bounded-above, termwise-epimorphic quasi-isomorphism data used in the
    truncation tower construction;
  - `Module.Flat R`, the canonical owner predicate for flat `R`-modules.

Source/core/bridge triage:
* `source-facing`: the existence of a termwise-epimorphic quasi-isomorphism from a K-flat complex
  with flat terms;
* `core/canonical`: the predicates `IsKFlat`, `IsTermwiseFlat`, `QuasiIso`, and the
  complex-level epimorphism owner `Epi π`;
* `bridge/view`: `cochainComplex_epi_iff_degreewise_epi` and the Chapter 13 upper-truncation
  resolution tower used to construct the witness.

Primitive data are only the resolving complex `K` and comparison morphism `π`. The four
properties above are derived API over existing owner abstractions, so they should not be bundled
into a parallel local wrapper class in this file.
-/

-- Proof sketch: choose the truncation-resolution tower from Derived Categories, Lemma `13.29.1`
-- with flat terms in each bounded-above stage. Each stage is K-flat by Lemma `15.59.7`, and the
-- sequential colimit is K-flat by Lemma `15.59.8`. Filtered colimits of flat modules are flat by
-- Algebra, Lemma `10.39.3`, and the induced map from the colimit complex to `M^•` is a
-- termwise-epimorphic quasi-isomorphism by the construction of the tower.
/-- Helper for Lemma 15.59.10: every cochain complex admits an upper truncation resolution tower
whose stages have free terms. -/
lemma exists_free_upperTruncationResolutionTower
    (M : CochainComplex (ModuleCat R) ℤ) :
    Nonempty (CategoryTheory.UpperTruncationResolutionTower (FreeObj (R := R)) M) := by
  -- The Chapter 13 tower theorem now applies directly to the free-module object property.
  simpa using CategoryTheory.exists_upperTruncationResolutionTower (FreeObj (R := R)) M

/-- Helper for Lemma 15.59.10: a universe-clean `ModuleCat` specialization of the bounded-above
flat-implies-K-flat bridge. -/
lemma moduleCat_isKFlat_of_boundedAbove_of_flat
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hbounded : CochainComplex.minus (ModuleCat.{u} R) P)
    (hFlat : P.IsTermwiseFlat) :
    P.IsKFlat := by
  -- Route correction: isolate the ambient-universe mismatch from `Lemma 15.59.7` in one helper,
  -- so the stage proof below can follow the source route directly once this bridge is supplied.
  simpa using CochainComplex.isKFlat_of_boundedAbove_of_flat P hbounded hFlat

/-- Helper for Lemma 15.59.10: every stage of a free upper truncation resolution tower is
K-flat. -/
lemma stage_isKFlat_of_free_upperTruncationResolutionTower
    {M : CochainComplex (ModuleCat R) ℤ}
    (T : CategoryTheory.UpperTruncationResolutionTower (FreeObj (R := R)) M) (n : ℕ) :
    (T.stage n).IsKFlat := by
  -- Each stage is bounded above by construction.
  have hminus : CochainComplex.minus (ModuleCat.{u} R) (T.stage n) := by
    exact (CochainComplex.minus_iff (ModuleCat.{u} R) (T.stage n)).2
      ⟨(n : ℤ) + 1, (T.isResolutionStage n).strictlyLE⟩
  -- Each stage term is free, hence flat.
  have hFlat : (T.stage n).IsTermwiseFlat := by
    intro i
    change Module.Flat R ((((T.stage n).X i : ModuleCat R) : Type u))
    let _ : Module.Free R ((((T.stage n).X i : ModuleCat R) : Type u)) :=
      (T.isResolutionStage n).term_mem i
    exact Module.Flat.of_free
  -- Apply the universe-clean bounded-above flat criterion specialized to `ModuleCat`.
  exact moduleCat_isKFlat_of_boundedAbove_of_flat (R := R) (T.stage n) hminus hFlat

/-- Helper for Lemma 15.59.10: the colimit complex of a free upper truncation resolution tower has
flat terms. -/
lemma colimit_isTermwiseFlat_of_free_upperTruncationResolutionTower
    {M : CochainComplex (ModuleCat R) ℤ}
    (T : CategoryTheory.UpperTruncationResolutionTower (FreeObj (R := R)) M) :
    CochainComplex.IsTermwiseFlat (colimit T.diagram) := by
  intro i
  let F : ℕ ⥤ ModuleCat.{u} R :=
    T.diagram ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i
  let e : colimit F ≅
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i).obj (colimit T.diagram) :=
    (CategoryTheory.preservesColimitIso
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i) T.diagram).symm
  let _ : ∀ n : ℕ, Module.Flat R ((F.obj n : ModuleCat R) : Type u) := by
    intro n
    -- Each evaluated stage term is free, hence flat.
    change Module.Flat R (((T.stage n).X i : ModuleCat R) : Type u)
    let _ : Module.Free R (((T.stage n).X i : ModuleCat R) : Type u) :=
      (T.isResolutionStage n).term_mem i
    exact Module.Flat.of_free
  let _ : Module.Flat R ((colimit F : ModuleCat R) : Type u) := inferInstance
  -- Transport flatness back across the canonical evaluation-of-colimit isomorphism.
  have hEvalFlat :
      Module.Flat R
        ((((HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i).obj
            (colimit T.diagram) : ModuleCat R) : Type u)) := by
    exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  simpa using hEvalFlat

/-- Helper for Lemma 15.59.10: a degree `i ≤ b` lies in the image of the upper-truncation
embedding `m ↦ b - m`. -/
private theorem embeddingUpIntLE_toNat_sub_eq
    (b i : ℤ) (hi : i ≤ b) :
    (ComplexShape.embeddingUpIntLE b).f (Int.toNat (b - i)) = i := by
  -- The retained upper-truncation range is indexed by the nonnegative difference `b - i`.
  dsimp [ComplexShape.embeddingUpIntLE]
  rw [Int.toNat_of_nonneg]
  · omega
  · omega

/-- Helper for Lemma 15.59.10: strictly below the cutoff, upper truncation keeps the original
term. -/
private noncomputable def upperTruncation_term_iso_of_lt
    (M : CochainComplex (ModuleCat R) ℤ) (b i : ℤ) (hi : i < b) :
    (M.truncLE b).X i ≅ M.X i :=
  let j : ℕ := Int.toNat (b - i)
  let hj : (ComplexShape.embeddingUpIntLE b).f j = i :=
    embeddingUpIntLE_toNat_sub_eq b i (le_of_lt hi)
  let hboundary : ¬ (ComplexShape.embeddingUpIntLE b).BoundaryLE j := by
    rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]
    intro hj0
    have : b = i := by
      simpa [j, hj0, ComplexShape.embeddingUpIntLE] using hj
    omega
  M.truncLEXIso (e := ComplexShape.embeddingUpIntLE b) hj hboundary

/-- Helper for Lemma 15.59.10: at the cutoff, upper truncation keeps the cycles object. -/
private noncomputable def upperTruncation_term_iso_cycles
    (M : CochainComplex (ModuleCat R) ℤ) (b : ℤ) :
    (M.truncLE b).X b ≅ M.cycles b :=
  let hi' : (ComplexShape.embeddingUpIntLE b).f 0 = b := by
    simp [ComplexShape.embeddingUpIntLE]
  let hboundary : (ComplexShape.embeddingUpIntLE b).BoundaryLE 0 := by
    simpa using (ComplexShape.boundaryLE_embeddingUpIntLE_iff b 0).2 rfl
  M.truncLEXIsoCycles (e := ComplexShape.embeddingUpIntLE b) hi' hboundary

/-- Helper for Lemma 15.59.10: strictly below the cutoff, the component of the upper-truncation
inclusion is the standard retained-term identification. -/
private theorem upperTruncationInclusion_component_eq_of_lt
    (M : CochainComplex (ModuleCat R) ℤ) (b i : ℤ) (hi : i < b) :
    (M.ιTruncLE b).f i = (upperTruncation_term_iso_of_lt M b i hi).hom := by
  let e := ComplexShape.embeddingUpIntLE b
  let j : ℕ := Int.toNat (b - i)
  have hj : e.f j = i := embeddingUpIntLE_toNat_sub_eq b i (le_of_lt hi)
  have hboundary : ¬ e.BoundaryLE j := by
    -- Strictly below the cutoff, the chosen index is not the boundary index of the truncation.
    rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]
    intro hj0
    have : b = i := by
      simpa [e, j, hj0, ComplexShape.embeddingUpIntLE] using hj
    omega
  -- Route correction: read the component from the dual `πTruncGE` formula and then unop it.
  apply Quiver.Hom.op_inj
  change ((M.op.πTruncGE e.op).f i) =
    (M.op.truncGEXIso e.op hj (by simpa using hboundary)).inv
  dsimp [CochainComplex.πTruncGE, HomologicalComplex.πTruncGE]
  rw [e.op.liftExtend_f (M.op.restrictionToTruncGE' e.op)
      (M.op.restrictionToTruncGE'_hasLift e.op) hj]
  rw [M.op.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e.op hj (by simpa using hboundary)]
  simp [HomologicalComplex.truncGEXIso, Category.assoc]
  rfl

/-- Helper for Lemma 15.59.10: below the truncation cutoff, the canonical inclusion into the
ambient complex is an isomorphism on the chosen component. -/
lemma upperTruncationInclusion_component_isIso_of_lt
    (M : CochainComplex (ModuleCat R) ℤ) (n : ℕ) {i : ℤ} (hi : i < (n : ℤ) + 1) :
    IsIso ((CategoryTheory.upperTruncationInclusion M n).f i) := by
  -- Identify the component with the canonical retained-term isomorphism.
  rw [CategoryTheory.upperTruncationInclusion]
  rw [upperTruncationInclusion_component_eq_of_lt (b := (n : ℤ) + 1) (i := i) M hi]
  infer_instance

/-- Helper for Lemma 15.59.10: at the cutoff degree, the upper-truncation inclusion is the
cycles inclusion under the standard cutoff-term identification. -/
lemma upperTruncationInclusion_component_eq_cycles
    (M : CochainComplex (ModuleCat R) ℤ) (n : ℕ) :
    ((CategoryTheory.upperTruncationInclusion M n).f ((n : ℤ) + 1)) =
      (upperTruncation_term_iso_cycles M ((n : ℤ) + 1)).hom ≫ M.iCycles ((n : ℤ) + 1) := by
  let b : ℤ := (n : ℤ) + 1
  let e := ComplexShape.embeddingUpIntLE b
  let hi' : e.f 0 = b := by
    simpa [b, e, ComplexShape.embeddingUpIntLE] using (embeddingUpIntLE_toNat_sub_eq b b le_rfl)
  have hi : e.BoundaryLE 0 := by
    simpa [b, e] using (ComplexShape.boundaryLE_embeddingUpIntLE_iff b 0).2 rfl
  -- Route correction: read the cutoff component from the dual `πTruncGE` boundary formula, then
  -- transport it across the canonical `opcycles`/`cycles` comparison.
  rw [CategoryTheory.upperTruncationInclusion]
  apply Quiver.Hom.op_inj
  change ((M.op.πTruncGE e.op).f b) =
    ((upperTruncation_term_iso_cycles M b).hom ≫ M.iCycles b).op
  dsimp [CochainComplex.πTruncGE, HomologicalComplex.πTruncGE]
  rw [e.op.liftExtend_f (M.op.restrictionToTruncGE' e.op)
      (M.op.restrictionToTruncGE'_hasLift e.op) hi']
  rw [M.op.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e.op hi' (by simpa using hi)]
  simp [Category.assoc]
  change (M.op.pOpcycles b ≫
      ((M.op.truncGE'XIsoOpcycles e.op hi' (by simpa using hi)).inv ≫
        (((M.op.truncGE' e.op).extendXIso e.op hi').inv))) =
    (M.sc b).iCycles.op ≫ (upperTruncation_term_iso_cycles M b).hom.op
  rw [← (M.sc b).op_pOpcycles_opcyclesOpIso_hom]
  have hcut :
      (M.opcyclesOpIso b).hom ≫ (upperTruncation_term_iso_cycles M b).hom.op =
        (M.op.truncGE'XIsoOpcycles e.op hi' (by simpa using hi)).inv ≫
          (((M.op.truncGE' e.op).extendXIso e.op hi').inv) := by
    simp [upperTruncation_term_iso_cycles, CochainComplex.truncLE,
      HomologicalComplex.truncLEXIsoCycles, HomologicalComplex.truncGEXIsoOpcycles,
      HomologicalComplex.opcyclesOpIso, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id_assoc]
    rfl
  simpa [HomologicalComplex.opcyclesOpIso, Category.assoc] using
    congrArg (fun f ↦ M.op.pOpcycles b ≫ f) hcut.symm

/-- Helper for Lemma 15.59.10: exact sequential colimits preserve homology in `ModuleCat R`. -/
local instance sequentialColim_preservesHomology :
    ((colim : (ℕ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).PreservesHomology) := by
  let G : (ℕ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R := colim
  -- Exact filtered colimits in modules preserve the finite limits and colimits entering homology.
  letI : PreservesFiniteLimits G := inferInstance
  letI : PreservesFiniteColimits G := inferInstance
  exact CategoryTheory.Functor.preservesHomologyOfExact G

/-- Helper for Lemma 15.59.10: in a sequential diagram of cochain complexes, the previous
differential at degree `i` forms a natural transformation on the degreewise diagrams. -/
private def prev_d_natTrans
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    S ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) (i - 1) ⟶
      S ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i where
  app n := (S.obj n).d (i - 1) i
  naturality _ _ f := by
    -- Naturality is exactly the commutativity of differentials with a chain map.
    simpa using (S.map f).comm (i - 1) i

/-- Helper for Lemma 15.59.10: in a sequential diagram of cochain complexes, the next
differential at degree `i` forms a natural transformation on the degreewise diagrams. -/
private def next_d_natTrans
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    S ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i ⟶
      S ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) (i + 1) where
  app n := (S.obj n).d i (i + 1)
  naturality _ _ f := by
    -- This is the same differential-commutativity statement one degree higher.
    simpa using (S.map f).comm i (i + 1)

/-- Helper for Lemma 15.59.10: the consecutive degreewise differentials in a sequential
diagram still compose to zero inside the functor category. -/
private theorem degree_d_comp_eq_zero
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    prev_d_natTrans (R := R) S i ≫ next_d_natTrans (R := R) S i = 0 := by
  -- Check the equation componentwise and use `d ≫ d = 0` in each stage.
  ext n
  simpa using (S.obj n).d_comp_d (i - 1) i (i + 1)

/-- Helper for Lemma 15.59.10: the degree-`i` short complex attached to a sequential
diagram of cochain complexes, formed inside the functor category `ℕ ⥤ ModuleCat R`. -/
private def degree_shortComplex
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    ShortComplex (ℕ ⥤ ModuleCat.{u} R) :=
  ShortComplex.mk
    (prev_d_natTrans (R := R) S i)
    (next_d_natTrans (R := R) S i)
    (degree_d_comp_eq_zero (R := R) S i)

/-- Helper for Lemma 15.59.10: evaluating the functor-category degree-`i` short complex at a
stage recovers the ordinary degree-`i` short complex of that stage. -/
private def degree_shortComplex_app_iso
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) (n : ℕ) :
    (degree_shortComplex (R := R) S i).map ((evaluation ℕ (ModuleCat.{u} R)).obj n) ≅
      (S.obj n).sc i :=
  -- After evaluation, both short complexes have the same terms and differentials.
  (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)) ≪≫
    ((S.obj n).isoSc' (i := i - 1) (j := i) (k := i + 1)
      (CochainComplex.prev ℤ i) (CochainComplex.next ℤ i)).symm

/-- Helper for Lemma 15.59.10: the first `mapShortComplex` compatibility condition for the
degree-`i` surface is the canonical colimit relation for the previous differential. -/
private theorem degree_shortComplex_colimit_map_prev
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) (n : ℕ) :
    colimit.ι (degree_shortComplex (R := R) S i).X₁ n ≫
        colim.map (prev_d_natTrans (R := R) S i) =
      (degree_shortComplex (R := R) S i).f.app n ≫
        colimit.ι (degree_shortComplex (R := R) S i).X₂ n := by
  -- This is exactly `colimit.ι_map`, rewritten on the chosen short-complex surface.
  simpa [degree_shortComplex] using
    (colimit.ι_map (prev_d_natTrans (R := R) S i) n)

/-- Helper for Lemma 15.59.10: the second `mapShortComplex` compatibility condition for the
degree-`i` surface is the canonical colimit relation for the next differential. -/
private theorem degree_shortComplex_colimit_map_next
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) (n : ℕ) :
    colimit.ι (degree_shortComplex (R := R) S i).X₂ n ≫
        colim.map (next_d_natTrans (R := R) S i) =
      (degree_shortComplex (R := R) S i).g.app n ≫
        colimit.ι (degree_shortComplex (R := R) S i).X₃ n := by
  -- This is the same cocone-leg identity for the next differential.
  simpa [degree_shortComplex] using
    (colimit.ι_map (next_d_natTrans (R := R) S i) n)

/-- Helper for Lemma 15.59.10: evaluating the chosen colimit cocone at degree `i` gives the
canonical cocone on the degree-`i` term diagram. -/
private def colimit_degree_term_cocone
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) [HasColimit S] (i : ℤ) :
    Cocone (S ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i) :=
  (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i).mapCocone (colimit.cocone S)

/-- Helper for Lemma 15.59.10: evaluation preserves the chosen sequential colimit, so the
degree-`i` evaluated cocone is colimiting. -/
private def colimit_degree_term_isColimit
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) [HasColimit S] (i : ℤ) :
    IsColimit (colimit_degree_term_cocone (R := R) S i) :=
  Limits.isColimitOfPreserves
    (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i)
    (colimit.isColimit S)

/-- Helper for Lemma 15.59.10: the colimit of the degree-`i` terms is canonically the degree-`i`
term of the colimit complex. -/
private noncomputable def colimit_degree_term_iso
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) [HasColimit S] (i : ℤ) :
    colimit (S ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i) ≅
      (colimit S).X i :=
  ((colimit_degree_term_isColimit (R := R) S i).coconePointUniqueUpToIso
    (colimit.isColimit (S ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i))).symm

/-- Helper for Lemma 15.59.10: on each cocone leg, the degreewise colimit comparison is the
canonical degree map into the colimit complex. -/
private theorem colimit_degree_term_iso_hom_ι
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) [HasColimit S] (i : ℤ) (n : ℕ) :
    colimit.ι (S ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i) n ≫
        (colimit_degree_term_iso (R := R) S i).hom =
      (colimit.ι S n).f i := by
  let e :
      (colimit S).X i ≅ colimit (S ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i) :=
    (colimit_degree_term_isColimit (R := R) S i).coconePointUniqueUpToIso
      (colimit.isColimit (S ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i))
  have h :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit_degree_term_isColimit (R := R) S i)
      (colimit.isColimit (S ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i)) n
  -- Compose the cocone-leg identity with the inverse comparison to recover the chosen direction.
  simpa [colimit_degree_term_iso, colimit_degree_term_cocone, e] using
    (congrArg (fun f ↦ f ≫ e.inv) h).symm

/-- Helper for Lemma 15.59.10: the degreewise colimit comparison intertwines the previous
differential with the colimit of the previous-differential natural transformation. -/
private theorem colimit_degree_term_iso_prev_comm
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) [HasColimit S] (i : ℤ) :
    (colimit_degree_term_iso (R := R) S (i - 1)).hom ≫ (colimit S).d (i - 1) i =
      colim.map (prev_d_natTrans (R := R) S i) ≫
        (colimit_degree_term_iso (R := R) S i).hom := by
  -- Compare both morphisms after precomposing with every cocone leg.
  apply colimit.hom_ext
  intro n
  calc
    colimit.ι (S ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) (i - 1)) n ≫
        (colimit_degree_term_iso (R := R) S (i - 1)).hom ≫ (colimit S).d (i - 1) i =
      (colimit.ι S n).f (i - 1) ≫ (colimit S).d (i - 1) i := by
        rw [Category.assoc, colimit_degree_term_iso_hom_ι]
    _ = (S.obj n).d (i - 1) i ≫ (colimit.ι S n).f i := by
        simpa using (colimit.ι S n).comm (i - 1) i
    _ = (prev_d_natTrans (R := R) S i).app n ≫
          colimit.ι (S ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i) n ≫
            (colimit_degree_term_iso (R := R) S i).hom := by
        rw [colimit_degree_term_iso_hom_ι]
    _ = (colimit.ι
          (S ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) (i - 1)) n ≫
            colim.map (prev_d_natTrans (R := R) S i)) ≫
              (colimit_degree_term_iso (R := R) S i).hom := by
        rw [colimit.ι_map]
        simp [Category.assoc]
    _ = colimit.ι
          (S ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) (i - 1)) n ≫
          (colim.map (prev_d_natTrans (R := R) S i) ≫
            (colimit_degree_term_iso (R := R) S i).hom) := by
        simp [Category.assoc]

/-- Helper for Lemma 15.59.10: the degreewise colimit comparison intertwines the next
differential with the colimit of the next-differential natural transformation. -/
private theorem colimit_degree_term_iso_next_comm
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) [HasColimit S] (i : ℤ) :
    (colimit_degree_term_iso (R := R) S i).hom ≫ (colimit S).d i (i + 1) =
      colim.map (next_d_natTrans (R := R) S i) ≫
        (colimit_degree_term_iso (R := R) S (i + 1)).hom := by
  -- The proof is the same stagewise cocone-leg calculation one degree higher.
  apply colimit.hom_ext
  intro n
  calc
    colimit.ι (S ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i) n ≫
        (colimit_degree_term_iso (R := R) S i).hom ≫ (colimit S).d i (i + 1) =
      (colimit.ι S n).f i ≫ (colimit S).d i (i + 1) := by
        rw [Category.assoc, colimit_degree_term_iso_hom_ι]
    _ = (S.obj n).d i (i + 1) ≫ (colimit.ι S n).f (i + 1) := by
        simpa using (colimit.ι S n).comm i (i + 1)
    _ = (next_d_natTrans (R := R) S i).app n ≫
          colimit.ι (S ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) (i + 1)) n ≫
            (colimit_degree_term_iso (R := R) S (i + 1)).hom := by
        rw [colimit_degree_term_iso_hom_ι]
    _ = (colimit.ι
          (S ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i) n ≫
            colim.map (next_d_natTrans (R := R) S i)) ≫
              (colimit_degree_term_iso (R := R) S (i + 1)).hom := by
        rw [colimit.ι_map]
        simp [Category.assoc]
    _ = colimit.ι
          (S ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) i) n ≫
          (colim.map (next_d_natTrans (R := R) S i) ≫
            (colimit_degree_term_iso (R := R) S (i + 1)).hom) := by
        simp [Category.assoc]

/-- Helper for Lemma 15.59.10: the canonical colimit short complex of the sequential degree-`i`
surface identifies with the degree-`i` short complex of the colimit complex. -/
private noncomputable def colimit_degree_shortComplex_iso
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) [HasColimit S] (i : ℤ) :
    colim.mapShortComplex (degree_shortComplex (R := R) S i)
      (colimit.isColimit _)
      (colimit.cocone _)
      (colimit.cocone _)
      (colim.map (prev_d_natTrans (R := R) S i))
      (colim.map (next_d_natTrans (R := R) S i))
      (degree_shortComplex_colimit_map_prev (R := R) S i)
      (degree_shortComplex_colimit_map_next (R := R) S i) ≅
        (colimit S).sc i :=
  -- Assemble the three degreewise colimit comparisons into a short-complex isomorphism.
  (ShortComplex.isoMk
      (colimit_degree_term_iso (R := R) S (i - 1))
      (colimit_degree_term_iso (R := R) S i)
      (colimit_degree_term_iso (R := R) S (i + 1))
      (colimit_degree_term_iso_prev_comm (R := R) S i)
      (colimit_degree_term_iso_next_comm (R := R) S i)) ≪≫
    ((colimit S).isoSc' (i := i - 1) (j := i) (k := i + 1)
      (CochainComplex.prev ℤ i) (CochainComplex.next ℤ i)).symm

/-- Helper for Lemma 15.59.10: evaluating the functor-category degree-`i` short complex at each
stage defines the ordinary sequential diagram of stage short complexes. -/
private def degree_shortComplex_evalFunctor
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    ℕ ⥤ ShortComplex (ModuleCat.{u} R) where
  obj n := (degree_shortComplex (R := R) S i).map ((evaluation ℕ (ModuleCat.{u} R)).obj n)
  map f := (degree_shortComplex (R := R) S i).mapNatTrans ((evaluation ℕ (ModuleCat.{u} R)).map f)
  map_id n := by
    -- Each component of the identity map is definitionally the identity.
    ext <;> simp
  map_comp f g := by
    -- Evaluation of a composite agrees componentwise with successive evaluations.
    ext <;> simp

/-- Helper for Lemma 15.59.10: the evaluated degree-`i` short complex is naturally the ordinary
degree-`i` short-complex diagram of the stages. -/
private noncomputable def degree_shortComplex_app_natIso
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    degree_shortComplex_evalFunctor (R := R) S i ≅
      S ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i :=
  NatIso.ofComponents
    (fun n ↦ degree_shortComplex_app_iso (R := R) S i n)
    (fun n m f ↦ by
      -- Both sides are the short-complex morphism induced by the same chain map.
      ext <;> simp)

/-- Helper for Lemma 15.59.10: functor-category homology agrees with stagewise homology after
evaluation. -/
private noncomputable def degree_shortComplex_homology_eval_iso
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    (degree_shortComplex (R := R) S i).homology ≅
      degree_shortComplex_evalFunctor (R := R) S i ⋙ ShortComplex.homologyFunctor (ModuleCat.{u} R) :=
  NatIso.ofComponents
    (fun n ↦
      ((degree_shortComplex (R := R) S i).mapHomologyIso
        ((evaluation ℕ (ModuleCat.{u} R)).obj n)).symm)
    (fun n m f ↦ by
      -- Isolate the functor-category-to-stagewise transport before the colimit argument.
      have h :=
        NatTrans.app_homology
          (τ := (evaluation ℕ (ModuleCat.{u} R)).map f)
          (S := degree_shortComplex (R := R) S i)
      simpa [degree_shortComplex_evalFunctor, Category.assoc] using
        congrArg
          (fun k ↦
            k ≫ (((degree_shortComplex (R := R) S i).mapHomologyIso
              ((evaluation ℕ (ModuleCat.{u} R)).obj m)).symm).hom)
          h)

/-- Helper for Lemma 15.59.10: the homology of the functor-category degree-`i` short complex is
the actual degree-`i` homology diagram of the sequential complex diagram. -/
private noncomputable def degree_shortComplex_homology_iso
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    (degree_shortComplex (R := R) S i).homology ≅
      S ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i :=
  let e₁ := degree_shortComplex_homology_eval_iso (R := R) S i
  let e₂ :=
    Functor.mapIso (ShortComplex.homologyFunctor (ModuleCat.{u} R))
      (degree_shortComplex_app_natIso (R := R) S i)
  let e₃ :
      (S ⋙ HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i) ⋙
          ShortComplex.homologyFunctor (ModuleCat.{u} R) ≅
        S ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i :=
    NatIso.ofComponents
      (fun _ ↦ Iso.refl _)
      (fun _ _ _ ↦ by
        -- On each stage, the map on homology of the standard short-complex functor is
        -- exactly `homologyMap`.
        rfl)
  -- Compose the evaluation comparison, the short-complex identification, and the definitional
  -- identification of short-complex homology with complex homology.
  e₁ ≪≫ e₂ ≪≫ e₃

/-- Helper for Lemma 15.59.10: the universal sequential colimit cocone defines a natural
transformation from evaluation at stage `n` to the colimit functor on degreewise diagrams. -/
private theorem evaluationToColimit_naturality
    (n : ℕ) {A B : ℕ ⥤ ModuleCat.{u} R} (τ : A ⟶ B) :
    ((evaluation ℕ (ModuleCat.{u} R)).obj n).map τ ≫ colimit.ι B n =
      colimit.ι A n ≫ (colim : (ℕ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).map τ := by
  -- This is exactly the naturality of the universal colimit cocone.
  simpa using (colimit.ι_map τ n).symm

/-- Helper for Lemma 15.59.10: evaluation at a fixed stage maps naturally to the sequential
colimit functor on degreewise diagrams. -/
private def evaluationToColimitNatTrans
    (n : ℕ) :
    (evaluation ℕ (ModuleCat.{u} R)).obj n ⟶ (colim : (ℕ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R) where
  app A := colimit.ι A n
  naturality _ _ τ := evaluationToColimit_naturality (R := R) n τ

/-- Helper for Lemma 15.59.10: the stage component of the homology-diagram identification
collapses the evaluation-side transport to the ordinary stage short-complex comparison. -/
private theorem degree_shortComplex_homology_iso_inv_app_comp_eval_inv
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) (n : ℕ) :
    (degree_shortComplex_homology_iso (R := R) S i).inv.app n ≫
        ((degree_shortComplex (R := R) S i).mapHomologyIso
          ((evaluation ℕ (ModuleCat.{u} R)).obj n)).inv =
      ShortComplex.homologyMap
        (degree_shortComplex_app_iso (R := R) S i n).inv := by
  -- Unfold the stage component and cancel the adjacent evaluation comparison.
  simp [degree_shortComplex_homology_iso, degree_shortComplex_homology_eval_iso,
    degree_shortComplex_app_natIso, Category.assoc]

/-- Helper for Lemma 15.59.10: after rewriting both endpoints of the universal stage leg through
the chosen short-complex identifications, the resulting short-complex morphism is the one induced
by the chain-map cocone leg `S_n ⟶ colim S`. -/
private theorem degree_shortComplex_transport_to_colimit_leg
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) (n : ℕ) :
    (degree_shortComplex_app_iso (R := R) S i n).inv ≫
        (degree_shortComplex (R := R) S i).mapNatTrans
          (evaluationToColimitNatTrans (R := R) n) ≫
        (colimit_degree_shortComplex_iso (R := R) S i).hom =
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).map
        (colimit.ι S n) := by
  -- Compare the transported short-complex map componentwise on the three terms.
  ext <;> simp [degree_shortComplex_app_iso, evaluationToColimitNatTrans,
    colimit_degree_shortComplex_iso, colimit_degree_term_iso_hom_ι, Category.assoc]

/-- Helper for Lemma 15.59.10: exact sequential colimits identify the `i`th homology of the
colimit complex with the colimit of the `i`th homology diagram. -/
private noncomputable def homology_of_sequential_colimit_iso_colimit_homology
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).obj (colimit S)) ≅
      colimit (S ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i) := by
  -- Package exactness on the degree-short-complex surface first, then transport to the actual
  -- homology diagram of the sequential tower.
  simpa [HomologicalComplex.homologyFunctor_obj] using
    ((ShortComplex.homologyMapIso
      (colimit_degree_shortComplex_iso (R := R) S i)).symm ≪≫
        (degree_shortComplex (R := R) S i).mapHomologyIso
          (colim : (ℕ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R) ≪≫
        colim.mapIso (degree_shortComplex_homology_iso (R := R) S i))

/-- Helper for Lemma 15.59.10: exact sequential colimits identify the colimit of the degreewise
homology diagram with the homology of the colimit complex. -/
private noncomputable def colimit_homology_iso_of_exact_sequential
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    colimit (S ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i) ≅
      (colimit S).homology i :=
  (homology_of_sequential_colimit_iso_colimit_homology (R := R) S i).symm

/-- Helper for Lemma 15.59.10: on each stage leg, the exact-colimit homology comparison is
exactly the homology map induced by the universal cocone map `S_n ⟶ colim S`. -/
private theorem colimit_homology_iso_of_exact_sequential_hom_ι
    (S : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) (n : ℕ) :
    colimit.ι (S ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i) n ≫
        (colimit_homology_iso_of_exact_sequential (R := R) S i).hom =
      HomologicalComplex.homologyMap (colimit.ι S n) i := by
  let T := degree_shortComplex (R := R) S i
  have h_leg :
      colimit.ι T.homology n =
        (T.mapHomologyIso ((evaluation ℕ (ModuleCat.{u} R)).obj n)).inv ≫
          ShortComplex.homologyMap
            (T.mapNatTrans (evaluationToColimitNatTrans (R := R) n)) ≫
          (T.mapHomologyIso (colim : (ℕ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R)).hom := by
    -- Apply `NatTrans.app_homology` to the evaluation-to-colimit natural transformation.
    simpa [T, evaluationToColimitNatTrans] using
      (NatTrans.app_homology
        (τ := evaluationToColimitNatTrans (R := R) n) (S := T))
  calc
    colimit.ι (S ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i) n ≫
        (colimit_homology_iso_of_exact_sequential (R := R) S i).hom =
      (degree_shortComplex_homology_iso (R := R) S i).inv.app n ≫
          colimit.ι T.homology n ≫
            (T.mapHomologyIso (colim : (ℕ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R)).inv ≫
              (ShortComplex.homologyMapIso
                (colimit_degree_shortComplex_iso (R := R) S i)).hom := by
        -- Move the stage leg across the colimit of the homology-diagram isomorphism.
        simpa [colimit_homology_iso_of_exact_sequential,
          homology_of_sequential_colimit_iso_colimit_homology, T, Category.assoc] using
          (colimit.ι_map (τ := (degree_shortComplex_homology_iso (R := R) S i).inv) n)
    _ =
      (degree_shortComplex_homology_iso (R := R) S i).inv.app n ≫
          (T.mapHomologyIso ((evaluation ℕ (ModuleCat.{u} R)).obj n)).inv ≫
            ShortComplex.homologyMap
              (T.mapNatTrans (evaluationToColimitNatTrans (R := R) n)) ≫
                (ShortComplex.homologyMapIso
                  (colimit_degree_shortComplex_iso (R := R) S i)).hom := by
        -- Replace the middle colimit leg by the explicit homology naturality formula.
        simpa [Category.assoc] using
          congrArg
            (fun f ↦
              (degree_shortComplex_homology_iso (R := R) S i).inv.app n ≫
                f ≫
                  (T.mapHomologyIso (colim : (ℕ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R)).inv ≫
                    (ShortComplex.homologyMapIso
                      (colimit_degree_shortComplex_iso (R := R) S i)).hom)
            h_leg
    _ =
      ShortComplex.homologyMap
          (degree_shortComplex_app_iso (R := R) S i n).inv ≫
            ShortComplex.homologyMap
              (T.mapNatTrans (evaluationToColimitNatTrans (R := R) n)) ≫
                (ShortComplex.homologyMapIso
                  (colimit_degree_shortComplex_iso (R := R) S i)).hom := by
        -- Cancel the evaluation-side comparison inside the stage component.
        rw [degree_shortComplex_homology_iso_inv_app_comp_eval_inv (R := R)]
    _ =
      ShortComplex.homologyMap
        ((degree_shortComplex_app_iso (R := R) S i n).inv ≫
          T.mapNatTrans (evaluationToColimitNatTrans (R := R) n) ≫
            (colimit_degree_shortComplex_iso (R := R) S i).hom) := by
        -- Collapse the three homology maps into the homology map of the composite.
        simp [Category.assoc, ShortComplex.homologyMap_comp]
    _ =
      ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).map
          (colimit.ι S n)) := by
        rw [degree_shortComplex_transport_to_colimit_leg (R := R)]
    _ = HomologicalComplex.homologyMap (colimit.ι S n) i := by
        rfl

/-- Helper for Lemma 15.59.10: exactness of a short complex of sequential module systems can be
checked after evaluating at each stage. -/
private theorem shortComplex_exact_iff_exact_app
    (S : ShortComplex (ℕ ⥤ ModuleCat.{u} R)) :
    S.Exact ↔ ∀ n : ℕ, (S.map ((evaluation ℕ (ModuleCat.{u} R)).obj n)).Exact := by
  let hEval :
      JointlyReflectIsomorphisms
        ((evaluation ℕ (ModuleCat.{u} R)).obj :
          ℕ → (ℕ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R) := by
    refine ⟨fun {X Y} f _ ↦ ?_⟩
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    simpa using
      (inferInstance : IsIso (((evaluation ℕ (ModuleCat.{u} R)).obj n).map f))
  -- Once the evaluation family is known to reflect isomorphisms, exactness is pointwise.
  exact hEval.exact_iff S

/-- Helper for Lemma 15.59.10: if each stage of a sequential diagram of cochain complexes is
acyclic, then the induced degree-`i` short complex in the functor category is exact. -/
private theorem degree_shortComplex_exact
    (G : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ)
    (hG : ∀ n : ℕ, (G.obj n).Acyclic) (i : ℤ) :
    (degree_shortComplex (R := R) G i).Exact := by
  -- Reflect exactness through evaluation, where the short complex becomes the stagewise one.
  rw [shortComplex_exact_iff_exact_app]
  intro n
  have hExactAt : (G.obj n).ExactAt i := by
    exact (HomologicalComplex.acyclic_iff (G.obj n)).mp (hG n) i
  have hExactSc : ((G.obj n).sc i).Exact := by
    exact (HomologicalComplex.exactAt_iff (G.obj n) i).mp hExactAt
  -- Transport the stagewise exactness back across the evaluation identification.
  exact (ShortComplex.exact_iff_of_iso
    (degree_shortComplex_app_iso (R := R) G i n)).mpr hExactSc

/-- Helper for Lemma 15.59.10: acyclicity is preserved under isomorphism of cochain complexes. -/
private theorem acyclic_of_iso
    {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (e : K ≅ L) (hK : K.Acyclic) :
    L.Acyclic := by
  -- Reduce to exactness of the degreewise short complexes and transport those along `e`.
  rw [HomologicalComplex.acyclic_iff] at hK ⊢
  intro i
  have hExactK : (K.sc i).Exact := by
    exact (HomologicalComplex.exactAt_iff K i).mp (hK i)
  let eSc :
      K.sc i ≅ L.sc i :=
    (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).mapIso e
  exact (HomologicalComplex.exactAt_iff L i).mpr <| ShortComplex.exact_of_iso eSc hExactK

/-- Helper for Lemma 15.59.10: sequential colimits of `R`-modules are exact. -/
private theorem moduleCat_sequential_exact_colimits :
    HasExactColimitsOfShape ℕ (ModuleCat.{u} R) := by
  let _ : HasColimitsOfShape ℕ AddCommGrpCat.{u} := by
    exact AddCommGrpCat.hasColimitsOfShape (J := ℕ)
  let _ : HasColimitsOfShape ℕ (ModuleCat.{u} R) := ModuleCat.hasColimitsOfShape R ℕ
  let _ : AB5OfSize.{u, u} AddCommGrpCat.{u} := AB5OfSize_shrink AddCommGrpCat.{u}
  let _ : HasExactColimitsOfShape ℕ AddCommGrpCat.{u} := by
    infer_instance
  -- Exactness is reflected by the forgetful functor to additive groups.
  exact HasExactColimitsOfShape.domain_of_functor ℕ
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})

/-- Helper for Lemma 15.59.10: exactness of a sequential short-complex diagram of `R`-modules
descends to the short complex obtained by taking colimits termwise. -/
private theorem colimit_mapShortComplex_exact_of_sequential
    (S : ShortComplex (ℕ ⥤ ModuleCat.{u} R)) (hS : S.Exact) :
    (colim.mapShortComplex S
      (colimit.isColimit S.X₁)
      (colimit.cocone S.X₂)
      (colimit.cocone S.X₃)
      (colim.map S.f)
      (colim.map S.g)
      (fun n ↦ by simp)
      (fun n ↦ by simp)).Exact := by
  let _ : HasExactColimitsOfShape ℕ (ModuleCat.{u} R) :=
    moduleCat_sequential_exact_colimits (R := R)
  have hf :
      ∀ n : ℕ,
        colimit.ι S.X₁ n ≫ colim.map S.f = S.f.app n ≫ colimit.ι S.X₂ n := by
    intro n
    simpa using (colimit.ι_map S.f n)
  have hg :
      ∀ n : ℕ,
        colimit.ι S.X₂ n ≫ colim.map S.g = S.g.app n ≫ colimit.ι S.X₃ n := by
    intro n
    simpa using (colimit.ι_map S.g n)
  -- Once sequential exactness is installed on `ModuleCat R`, the canonical colimit short
  -- complex is exact by the generic `colim.exact_mapShortComplex` theorem.
  exact Limits.colim.exact_mapShortComplex hS
    (colimit.isColimit S.X₁)
    (colimit.isColimit S.X₂)
    (colimit.isColimit S.X₃)
    (colim.map S.f)
    (colim.map S.g)
    hf
    hg

/-- Helper for Lemma 15.59.10: a sequential colimit of acyclic cochain complexes of `R`-modules
is acyclic. -/
private theorem acyclic_colimit_of_sequential
    (G : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ)
    [HasColimit G]
    (hG : ∀ n : ℕ, (G.obj n).Acyclic) :
    (colimit G).Acyclic := by
  -- Prove acyclicity degreewise by exactness of the canonical degree-`i` short complexes.
  rw [HomologicalComplex.acyclic_iff]
  intro i
  have hExactSource :
      (colim.mapShortComplex (degree_shortComplex (R := R) G i)
        (colimit.isColimit _)
        (colimit.cocone _)
        (colimit.cocone _)
        (colim.map (prev_d_natTrans (R := R) G i))
        (colim.map (next_d_natTrans (R := R) G i))
        (degree_shortComplex_colimit_map_prev (R := R) G i)
        (degree_shortComplex_colimit_map_next (R := R) G i)).Exact := by
    -- First prove exactness in the functor category, then pass to colimits using sequential
    -- exactness.
    exact colimit_mapShortComplex_exact_of_sequential (R := R)
      (degree_shortComplex (R := R) G i)
      (degree_shortComplex_exact (R := R) G hG i)
  have hExactTarget : ((colimit G).sc i).Exact := by
    -- Transport exactness across the canonical identification of the colimit short complex.
    exact (ShortComplex.exact_iff_of_iso
      (colimit_degree_shortComplex_iso (R := R) G i)).mp hExactSource
  exact (HomologicalComplex.exactAt_iff (colimit G) i).mpr hExactTarget

/-- Helper for Lemma 15.59.10: if `F` has a colimit, then so does the tensorized diagram
`F ⋙ tensorLeft M`. -/
private theorem tensorLeft_hasColimit_of_hasColimit
    (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (F : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ)
    [HasColimit F] :
    HasColimit (F ⋙ MonoidalCategory.tensorLeft M) := by
  let _ :
      PreservesColimits
        (MonoidalCategory.tensorLeft M :
          CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) := inferInstance
  -- The tensor-left functor preserves colimits, so the tensorized diagram inherits a colimit.
  exact show HasColimit (F ⋙ MonoidalCategory.tensorLeft M) from inferInstance

/-- Helper for Lemma 15.59.10: tensoring on the left by a fixed cochain complex commutes with
sequential colimits of cochain complexes. -/
private noncomputable def tensorObj_colimit_iso
    (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (F : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ)
    [HasColimit F] [HasColimit (F ⋙ MonoidalCategory.tensorLeft M)] :
    colimit (F ⋙ MonoidalCategory.tensorLeft M) ≅
      HomologicalComplex.tensorObj M (colimit F) :=
  let _ :
      PreservesColimits
        (MonoidalCategory.tensorLeft M :
          CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) := inferInstance
  (CategoryTheory.preservesColimitIso (MonoidalCategory.tensorLeft M) F).symm

/-- Helper for Lemma 15.59.10: a sequential colimit of K-flat cochain complexes of `R`-modules
is K-flat. -/
private theorem sequentialColimit_isKFlat
    (F : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ)
    [HasColimit F]
    (hF : ∀ n : ℕ, (F.obj n).IsKFlat) :
    (colimit F).IsKFlat := by
  -- Test K-flatness against an arbitrary acyclic complex and commute tensoring with the
  -- sequential colimit.
  rw [CochainComplex.isKFlat_iff]
  intro M _ hM
  let _ : HasColimit (F ⋙ MonoidalCategory.tensorLeft M) :=
    tensorLeft_hasColimit_of_hasColimit (R := R) M F
  have hTensorAcyclic :
      (colimit (F ⋙ MonoidalCategory.tensorLeft M)).Acyclic := by
    -- Each stage is acyclic by the stagewise K-flatness hypothesis, so the sequential colimit is.
    refine acyclic_colimit_of_sequential (R := R) (G := F ⋙ MonoidalCategory.tensorLeft M) ?_
    intro n
    exact CochainComplex.acyclic_tensorObj_of_isKFlat (hF n) hM
  -- Transport acyclicity across the canonical tensor/colimit comparison isomorphism.
  exact acyclic_of_iso (R := R) (tensorObj_colimit_iso (R := R) M F) hTensorAcyclic

/-- Helper for Lemma 15.59.10: below the truncation cutoff, the stage map to the target is a
quasi-isomorphism in the chosen degree. -/
lemma toTarget_quasiIsoAt_of_le_stage
    {M : CochainComplex (ModuleCat R) ℤ}
    (T : CategoryTheory.UpperTruncationResolutionTower (FreeObj (R := R)) M)
    (i : ℤ) {n : ℕ} (h : i ≤ (n : ℤ) + 1) :
    QuasiIsoAt (T.toTarget n) i := by
  -- The stage comparison is already a quasi-isomorphism, and the canonical truncation inclusion
  -- is a quasi-isomorphism in every degree at or below the cutoff.
  change QuasiIsoAt (T.comparison.app n ≫ M.ιTruncLE ((n : ℤ) + 1)) i
  have hcomparison : QuasiIsoAt (T.comparison.app n) i :=
    (T.isResolutionStage n).quasiIso.quasiIsoAt i
  have htrunc : QuasiIsoAt (M.ιTruncLE ((n : ℤ) + 1)) i := by
    simpa using CochainComplex.quasiIsoAt_ιTruncLE M ((n : ℤ) + 1) i h
  -- Rewrite to the homology map and compose the two stagewise isomorphisms explicitly.
  rw [quasiIsoAt_iff_isIso_homologyMap] at hcomparison htrunc ⊢
  letI : IsIso (HomologicalComplex.homologyMap (T.comparison.app n) i) := hcomparison
  letI : IsIso (HomologicalComplex.homologyMap (M.ιTruncLE ((n : ℤ) + 1)) i) := htrunc
  let e₁ : _ ≅ _ := asIso (HomologicalComplex.homologyMap (T.comparison.app n) i)
  let e₂ : _ ≅ _ := asIso (HomologicalComplex.homologyMap (M.ιTruncLE ((n : ℤ) + 1)) i)
  refine ⟨⟨e₂.inv ≫ e₁.inv, ?_, ?_⟩⟩
  · simp [HomologicalComplex.homologyMap_comp, Category.assoc, e₁, e₂]
  · simp [HomologicalComplex.homologyMap_comp, Category.assoc, e₁, e₂]

/-- Helper for Lemma 15.59.10: after a stage whose cutoff contains degree `i`, the induced
diagram on `i`th homology is eventually constant. -/
lemma homologyDiagram_isEventuallyConstantFrom_of_le_stage
    {M : CochainComplex (ModuleCat R) ℤ}
    (T : CategoryTheory.UpperTruncationResolutionTower (FreeObj (R := R)) M)
    (i : ℤ) {n : ℕ} (h : i ≤ (n : ℤ) + 1) :
    CategoryTheory.Functor.IsEventuallyConstantFrom
      (T.diagram ⋙ HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) i) n := by
  intro j f
  have hsource : QuasiIsoAt (T.toTarget n) i :=
    toTarget_quasiIsoAt_of_le_stage (R := R) T i h
  have htarget : QuasiIsoAt (T.toTarget j) i :=
    toTarget_quasiIsoAt_of_le_stage (R := R) T i (by omega)
  have hcomp : T.diagram.map f ≫ T.toTarget j = T.toTarget n := by
    change T.diagram.map f ≫ T.cocone.ι.app j = T.cocone.ι.app n
    exact T.cocone.w f
  -- Naturality of the cocone identifies the transition map with a map between two stages that
  -- are already quasi-isomorphic to the target in degree `i`.
  have hstep : QuasiIsoAt (T.diagram.map f) i := by
    letI : QuasiIsoAt (T.diagram.map f ≫ T.toTarget j) i := by
      simpa [hcomp] using hsource
    exact quasiIsoAt_of_comp_right (T.diagram.map f) (T.toTarget j) i
  rw [quasiIsoAt_iff_isIso_homologyMap] at hstep
  simpa [Functor.comp_map] using hstep

/-- Helper for Lemma 15.59.10: for each fixed degree, the homology cocone of a free upper
truncation resolution tower is colimiting because the stage maps to the target become
isomorphisms on that homology group after the cutoff passes the degree. -/
noncomputable def toTarget_homologyCocone_isColimit
    {M : CochainComplex (ModuleCat R) ℤ}
    (T : CategoryTheory.UpperTruncationResolutionTower (FreeObj (R := R)) M)
    (i : ℤ) :
    IsColimit
      (((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) i).mapCocone
        T.cocone)) := by
  let n0 : ℕ := Int.toNat i
  have hle : i ≤ (n0 : ℤ) + 1 := by
    -- Any stage at `Int.toNat i` or later already contains degree `i`.
    by_cases hnonneg : 0 ≤ i
    · rw [Int.toNat_of_nonneg hnonneg]
      omega
    · have hnonpos : i ≤ 0 := le_of_not_ge hnonneg
      dsimp [n0]
      rw [Int.toNat_of_nonpos hnonpos]
      omega
  let hstable :
      CategoryTheory.Functor.IsEventuallyConstantFrom
        (T.diagram ⋙ HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) i) n0 :=
    homologyDiagram_isEventuallyConstantFrom_of_le_stage (R := R) T i hle
  have hstage : QuasiIsoAt (T.toTarget n0) i :=
    toTarget_quasiIsoAt_of_le_stage (R := R) T i hle
  rw [quasiIsoAt_iff_isIso_homologyMap] at hstage
  haveI :
      IsIso
        ((((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) i).mapCocone
            T.cocone).ι.app n0)) := by
    -- The chosen stage leg is exactly the homology map of the stage comparison to the target.
    simpa [n0] using hstage
  -- Eventual constancy upgrades the mapped cocone to a colimit cocone once one stage leg is an
  -- isomorphism.
  exact hstable.isColimitOfIsIso
    (((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) i).mapCocone
      T.cocone))

/-- Helper for Lemma 15.59.10: the canonical map from the colimit of a free upper truncation
resolution tower to the target complex is a quasi-isomorphism. -/
lemma fromColimit_quasiIso_of_free_upperTruncationResolutionTower
    {M : CochainComplex (ModuleCat R) ℤ}
    (T : CategoryTheory.UpperTruncationResolutionTower (FreeObj (R := R)) M) :
    QuasiIso T.fromColimit := by
  -- Rewrite the homology of the colimit as the colimit of stage homologies, then identify the
  -- resulting universal map with the mapped target cocone, which is already colimiting by
  -- eventual constancy after the cutoff passes the chosen degree.
  rw [quasiIso_iff_isIso_homologyMap]
  intro i
  have hdesc :
      IsIso
        (colimit.desc
          (T.diagram ⋙ HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) i)
          ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) i).mapCocone
            T.cocone)) := by
    let hcolim := toTarget_homologyCocone_isColimit (R := R) T i
    exact hcolim.hom_isIso
  have hcomp :
      IsIso
        ((colimit_homology_iso_of_exact_sequential (R := R) (S := T.diagram) i).hom ≫
          HomologicalComplex.homologyMap T.fromColimit i) := by
    -- Compare both maps after precomposing with each stage leg of the homology colimit.
    rw [show
      (colimit_homology_iso_of_exact_sequential (R := R) (S := T.diagram) i).hom ≫
          HomologicalComplex.homologyMap T.fromColimit i =
        colimit.desc
          (T.diagram ⋙ HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) i)
          ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) i).mapCocone
            T.cocone) by
      apply colimit.hom_ext
      intro n
      calc
        colimit.ι
            (T.diagram ⋙ HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) i) n ≫
            (colimit_homology_iso_of_exact_sequential (R := R) (S := T.diagram) i).hom ≫
              HomologicalComplex.homologyMap T.fromColimit i =
          HomologicalComplex.homologyMap (colimit.ι T.diagram n) i ≫
            HomologicalComplex.homologyMap T.fromColimit i := by
              rw [Category.assoc, colimit_homology_iso_of_exact_sequential_hom_ι]
        _ = HomologicalComplex.homologyMap (colimit.ι T.diagram n ≫ T.fromColimit) i := by
              rw [HomologicalComplex.homologyMap_comp]
        _ = HomologicalComplex.homologyMap (T.toTarget n) i := by
              rw [CategoryTheory.UpperTruncationResolutionTower.ι_comp_fromColimit]
        _ = ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) i).mapCocone
              T.cocone).ι.app n := by
              rfl
        _ =
            colimit.ι
                (T.diagram ⋙ HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) i) n ≫
              colimit.desc
                (T.diagram ⋙ HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) i)
                ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) i).mapCocone
                  T.cocone) := by
              simp [Category.assoc]]
    infer_instance
  exact
    (isIso_comp_left_iff
      ((colimit_homology_iso_of_exact_sequential (R := R) (S := T.diagram) i).hom)
      (HomologicalComplex.homologyMap T.fromColimit i)).1 hcomp

/-- Lemma 15.59.10: every cochain complex of `R`-modules admits a termwise-epimorphic
quasi-isomorphism from a K-flat cochain complex whose terms are flat `R`-modules. -/
lemma exists_termwiseEpi_kFlatResolution
    (M : CochainComplex (ModuleCat R) ℤ) :
    ∃ (K : CochainComplex (ModuleCat R) ℤ) (π : K ⟶ M),
      K.IsKFlat ∧ K.IsTermwiseFlat ∧ QuasiIso π ∧ ∀ i : ℤ, Epi (π.f i) := by
  obtain ⟨T⟩ := exists_free_upperTruncationResolutionTower (R := R) M
  refine ⟨colimit T.diagram, T.fromColimit, ?_, ?_, ?_, ?_⟩
  · -- Each stage is K-flat, so Lemma `15.59.8` upgrades the sequential colimit to a K-flat
    -- complex.
    exact sequentialColimit_isKFlat (R := R) T.diagram
      (stage_isKFlat_of_free_upperTruncationResolutionTower (R := R) T)
  · -- Filtered colimits of flat modules are flat degreewise.
    exact colimit_isTermwiseFlat_of_free_upperTruncationResolutionTower (R := R) T
  · -- The homology system stabilizes because the stage comparisons become quasi-isomorphisms in
    -- each fixed degree.
    exact fromColimit_quasiIso_of_free_upperTruncationResolutionTower (R := R) T
  · -- Evaluate `T.ι_comp_fromColimit` at a stage whose cutoff already contains degree `i`, then
    -- descend epimorphy from the stagewise target map to the colimit comparison component.
    intro i
    let n0 : ℕ := Int.toNat i
    have hi : i < (n0 : ℤ) + 1 := by
      by_cases hnonneg : 0 ≤ i
      · rw [Int.toNat_of_nonneg hnonneg]
        omega
      · have hnonpos : i ≤ 0 := le_of_not_ge hnonneg
        dsimp [n0]
        rw [Int.toNat_of_nonpos hnonpos]
        omega
    have hToTargetEpi : Epi ((T.toTarget n0).f i) := by
      -- The stage comparison is termwise epi, and the truncation inclusion is an isomorphism
      -- below the cutoff.
      let e := upperTruncation_term_iso_of_lt M ((n0 : ℤ) + 1) i hi
      letI : Epi ((T.comparison.app n0).f i) := (T.isResolutionStage n0).term_epi i
      letI : Epi e.hom := by infer_instance
      have hToTargetEq :
          (T.toTarget n0).f i = ((T.comparison.app n0).f i) ≫ e.hom := by
        -- Replace the cutoff component by the canonical retained-term isomorphism.
        rw [CategoryTheory.UpperTruncationResolutionTower.toTarget]
        dsimp [e]
        rw [upperTruncationInclusion_component_eq_of_lt (M := M) (b := (n0 : ℤ) + 1) (i := i) hi]
      rw [hToTargetEq]
      exact
        (CategoryTheory.epi_comp
          ((T.comparison.app n0).f i)
          e.hom)
    have hComp :
        ((colimit.ι T.diagram n0).f i) ≫ (T.fromColimit.f i) = (T.toTarget n0).f i := by
      -- Read the colimit comparison equality on the chosen component.
      change ((colimit.ι T.diagram n0 ≫ T.fromColimit).f i) = ((T.toTarget n0).f i)
      let hι :
          colimit.ι T.diagram n0 ≫ T.fromColimit = T.toTarget n0 :=
        CategoryTheory.UpperTruncationResolutionTower.ι_comp_fromColimit (T := T) (n := n0)
      rw [hι]
    letI : Epi (((colimit.ι T.diagram n0).f i) ≫ (T.fromColimit.f i)) := by
      rw [hComp]
      exact hToTargetEpi
    exact CategoryTheory.epi_of_epi ((colimit.ι T.diagram n0).f i) (T.fromColimit.f i)

-- The source-facing lemma above keeps the textbook termwise-epimorphism conclusion. This
-- companion re-expresses the same existence statement through the canonical complex-level owner
-- `Epi π`.
/-- Canonical owner-level form of Lemma 15.59.10: every cochain complex of `R`-modules admits a
quasi-isomorphism from a K-flat cochain complex with flat terms whose comparison morphism is
epimorphic. -/
lemma exists_epi_kFlatResolution
    (M : CochainComplex (ModuleCat R) ℤ) :
    ∃ (K : CochainComplex (ModuleCat R) ℤ) (π : K ⟶ M),
      K.IsKFlat ∧ K.IsTermwiseFlat ∧ QuasiIso π ∧ Epi π := by
  obtain ⟨K, π, hKFlat, hTermwiseFlat, hπ, hEpi⟩ := exists_termwiseEpi_kFlatResolution M
  exact ⟨K, π, hKFlat, hTermwiseFlat, hπ,
    (cochainComplex_epi_iff_degreewise_epi π).2 hEpi⟩

end CochainComplex
