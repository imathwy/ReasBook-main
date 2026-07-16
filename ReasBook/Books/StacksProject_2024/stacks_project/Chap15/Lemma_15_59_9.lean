import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Homology.BifunctorFlip
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.Monoidal
import StacksProject_2024.stacks_project.Chap10.Lemma_10_11_3
import StacksProject_2024.stacks_project.Chap10.Lemma_10_8_8
import StacksProject_2024.stacks_project.Chap10.Lemma_10_12_9_Tensor_products_commute_with_colimits
import StacksProject_2024.stacks_project.Chap13.Lemma_13_35_7
import StacksProject_2024.stacks_project.Chap15.Lemma_15_58_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_58_4
import StacksProject_2024.stacks_project.Chap15.Definition_15_59_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex MonoidalCategory

noncomputable section

universe u v

namespace CochainComplex

variable {R : Type u} [CommRing R]

local notation "single₀" => singleFunctor (ModuleCat R) (0 : ℤ)

/-
Domain sampling pass:
* primary domain: K-flat cochain complexes of `R`-modules, tested by tensoring with finitely
  presented `R`-modules;
* sampled owner declarations:
  - `CochainComplex.singleFunctor` from mathlib, used here through the standard local notation
    `single₀` for a module concentrated in degree `0`;
  - `CochainComplex.IsKFlat` from `Definition_15_59_1`, the source-facing owner predicate;
  - `CochainComplex.isKFlat_colimit_of_isFiltered` from `Lemma_15_59_8`, the chapter closure
    theorem
    used by the textbook reduction from arbitrary modules to finitely presented modules;
  - `CategoryTheory.ShortComplex.TensorShortExactForFinitelyPresented` from
    `Theorem_10_82_3`, showing the project’s canonical style for “for every finitely presented
    module” is an instance-binder quantification rather than an explicit witness argument.

Source/core/bridge triage:
* `source-facing`: the criterion that acyclicity after tensoring with finitely presented modules
  already implies K-flatness;
* `core/canonical`: `CochainComplex.IsKFlat`;
* `bridge/view`: `HomologicalComplex.tensorObj K ((single₀).obj M)`, the canonical tensor with
  `M` placed in degree `0`.

Primitive data are only the complex `K` and the finitely-presented tensor-acyclicity hypothesis.
The K-flatness conclusion is derived API over the existing owner `CochainComplex.IsKFlat`, so this
file should stay as a single owner-level criterion and avoid any auxiliary wrapper predicate.
-/

/-- Helper for Lemma 15.59.9: the textbook hypothesis specializes immediately to any chosen
finitely presented degree-zero module. -/
lemma tensor_single_zero_acyclic_of_finitePresentation
    (K : CochainComplex (ModuleCat R) ℤ)
    (hfp : ∀ (M : ModuleCat R) [Module.FinitePresentation R M],
      (HomologicalComplex.tensorObj K ((single₀).obj M)).Acyclic)
    (M : ModuleCat R) [Module.FinitePresentation R M] :
    (HomologicalComplex.tensorObj K ((single₀).obj M)).Acyclic := by
  -- This is just the given test hypothesis, isolated as a reusable local bridge.
  exact hfp M

/-- Helper for Lemma 15.59.9: for a finitely presented module in degree `0`, the hypothesis
forces exactness at every degree of the corresponding tensor complex. -/
lemma tensor_single_zero_exactAt_of_finitePresentation
    (K : CochainComplex (ModuleCat R) ℤ)
    (hfp : ∀ (M : ModuleCat R) [Module.FinitePresentation R M],
      (HomologicalComplex.tensorObj K ((single₀).obj M)).Acyclic)
    (M : ModuleCat R) [Module.FinitePresentation R M]
    (n : ℤ) :
    (HomologicalComplex.tensorObj K ((single₀).obj M)).ExactAt n := by
  -- Read exactness at degree `n` off the acyclicity of the tensor complex with `M` in degree `0`.
  have hAcyclic :
      (HomologicalComplex.tensorObj K ((single₀).obj M)).Acyclic :=
    tensor_single_zero_acyclic_of_finitePresentation (K := K) hfp M
  rw [HomologicalComplex.acyclic_iff] at hAcyclic
  exact hAcyclic n

/-- Helper for Lemma 15.59.9: the finitely presented test in particular applies to the ring `R`
viewed as a module over itself. -/
lemma tensor_single_zero_acyclic_of_ring
    (K : CochainComplex (ModuleCat R) ℤ)
    (hfp : ∀ (M : ModuleCat R) [Module.FinitePresentation R M],
      (HomologicalComplex.tensorObj K ((single₀).obj M)).Acyclic) :
    (HomologicalComplex.tensorObj K ((single₀).obj (ModuleCat.of R R))).Acyclic := by
  -- The ring `R`, viewed as a module over itself, is finitely presented.
  exact tensor_single_zero_acyclic_of_finitePresentation (K := K) hfp (ModuleCat.of R R)

/-- Helper for Lemma 15.59.9: acyclicity transports across an isomorphism of cochain complexes. -/
lemma acyclic_of_iso
    {K L : CochainComplex (ModuleCat R) ℤ}
    (e : K ≅ L) (hK : K.Acyclic) :
    L.Acyclic := by
  -- Read acyclicity degreewise and move exactness across the complex isomorphism.
  intro n
  exact HomologicalComplex.ExactAt.of_iso (hK n) e

/-- Helper for Lemma 15.59.9: if a shift of a cochain complex is acyclic, then the original
complex is acyclic. -/
lemma acyclic_of_shift
    (K : CochainComplex (ModuleCat R) ℤ) (n : ℤ)
    (hShift : (K⟦n⟧).Acyclic) :
    K.Acyclic := by
  -- Route correction: descend acyclicity from the shifted complex through the canonical homology
  -- shift isomorphism instead of trying to unfold the shifted differentials directly.
  rw [HomologicalComplex.acyclic_iff] at hShift ⊢
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hZeroShift : IsZero ((K⟦n⟧).homology (i - n)) := by
    -- Exactness of the shifted complex at degree `i - n` gives vanishing of that shifted homology.
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hShift (i - n)
  -- The shifted homology in degree `i - n` is canonically the original homology in degree `i`.
  exact hZeroShift.of_iso
    (((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) (0 : ℤ)).shiftIso
      n (i - n) i (by omega)).app K).symm

/-- Helper for Lemma 15.59.9: acyclicity is preserved by shifting a cochain complex. -/
lemma acyclic_shift
    (K : CochainComplex (ModuleCat R) ℤ) (n : ℤ)
    (hK : K.Acyclic) :
    (K⟦n⟧).Acyclic := by
  -- Shift back by `-n`, identify the double shift with the original complex, and then descend.
  have hShiftBack : ((K⟦n⟧)⟦-n⟧).Acyclic := by
    exact acyclic_of_iso (R := R) (shiftShiftNeg K n).symm hK
  exact acyclic_of_shift (R := R) (K⟦n⟧) (-n) hShiftBack

/-- Helper for Lemma 15.59.9: exactness of a short complex in a filtered module diagram can be
checked after evaluating at every stage. -/
private theorem shortComplex_exact_iff_exact_app
    {J : Type*} [Category J]
    (S : ShortComplex (J ⥤ ModuleCat R)) :
    S.Exact ↔ ∀ j : J, (S.map ((evaluation J (ModuleCat R)).obj j)).Exact := by
  let hEval :
      JointlyReflectIsomorphisms
        ((evaluation J (ModuleCat R)).obj :
          J → (J ⥤ ModuleCat R) ⥤ ModuleCat R) := by
    refine ⟨fun {X Y} f _ ↦ ?_⟩
    rw [NatTrans.isIso_iff_isIso_app]
    intro j
    simpa using
      (inferInstance : IsIso (((evaluation J (ModuleCat R)).obj j).map f))
  -- Once evaluation reflects isomorphisms jointly, exactness is pointwise.
  exact hEval.exact_iff S

/-- Helper for Lemma 15.59.9: the degree-`n - 1 → n` differentials in a diagram of cochain
complexes form a natural transformation on the underlying module diagrams. -/
private theorem prev_d_naturality
    {J : Type*} [Category J]
    (G : J ⥤ CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    ∀ ⦃i j : J⦄ (f : i ⟶ j),
      (G.map f).f (n - 1) ≫ (G.obj j).d (n - 1) n =
        (G.obj i).d (n - 1) n ≫ (G.map f).f n := by
  intro i j f
  -- This is exactly the degree-`n - 1 → n` commutativity for a morphism of complexes.
  simpa using (G.map f).comm (n - 1) n

/-- Helper for Lemma 15.59.9: the degree-`n → n + 1` differentials in a diagram of cochain
complexes form a natural transformation on the underlying module diagrams. -/
private theorem next_d_naturality
    {J : Type*} [Category J]
    (G : J ⥤ CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    ∀ ⦃i j : J⦄ (f : i ⟶ j),
      (G.map f).f n ≫ (G.obj j).d n (n + 1) =
        (G.obj i).d n (n + 1) ≫ (G.map f).f (n + 1) := by
  intro i j f
  -- This is the adjacent degree commutativity relation for a morphism of complexes.
  simpa using (G.map f).comm n (n + 1)

/-- Helper for Lemma 15.59.9: the previous differential in a diagram of cochain complexes yields
the corresponding natural transformation of module-valued diagrams. -/
private theorem prev_d_natTrans_naturality
    {J : Type*} [Category J]
    (G : J ⥤ CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    ∀ ⦃i j : J⦄ (f : i ⟶ j),
      (G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) (n - 1)).map f ≫
          (G.obj j).d (n - 1) n =
        (G.obj i).d (n - 1) n ≫
          (G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n).map f := by
  intro i j f
  exact prev_d_naturality (G := G) n f

/-- Helper for Lemma 15.59.9: the next differential in a diagram of cochain complexes yields the
corresponding natural transformation of module-valued diagrams. -/
private theorem next_d_natTrans_naturality
    {J : Type*} [Category J]
    (G : J ⥤ CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    ∀ ⦃i j : J⦄ (f : i ⟶ j),
      (G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n).map f ≫
          (G.obj j).d n (n + 1) =
        (G.obj i).d n (n + 1) ≫
          (G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) (n + 1)).map f := by
  intro i j f
  exact next_d_naturality (G := G) n f

/-- Helper for Lemma 15.59.9: the previous differentials of a diagram of cochain complexes form a
natural transformation in the functor category. -/
private def prev_d_natTrans
    {J : Type*} [Category J]
    (G : J ⥤ CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) (n - 1) ⟶
      G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n where
  app i := (G.obj i).d (n - 1) n
  naturality := prev_d_natTrans_naturality (G := G) n

/-- Helper for Lemma 15.59.9: the next differentials of a diagram of cochain complexes form a
natural transformation in the functor category. -/
private def next_d_natTrans
    {J : Type*} [Category J]
    (G : J ⥤ CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n ⟶
      G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) (n + 1) where
  app i := (G.obj i).d n (n + 1)
  naturality := next_d_natTrans_naturality (G := G) n

/-- Helper for Lemma 15.59.9: the consecutive degree differentials in a diagram of cochain
complexes compose to zero in the functor category. -/
private theorem degree_d_comp_eq_zero
    {J : Type*} [Category J]
    (G : J ⥤ CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    prev_d_natTrans (G := G) n ≫ next_d_natTrans (G := G) n = 0 := by
  -- Evaluate on each stage and use the usual `d ≫ d = 0` in that cochain complex.
  ext j x
  change
    ModuleCat.Hom.hom
        (((G.obj j).d (n - 1) n) ≫ ((G.obj j).d n (n + 1))) x =
      ModuleCat.Hom.hom (0 : (G.obj j).X (n - 1) ⟶ (G.obj j).X (n + 1)) x
  exact LinearMap.congr_fun
    (ModuleCat.hom_ext_iff.mp ((G.obj j).d_comp_d (n - 1) n (n + 1))) x

/-- Helper for Lemma 15.59.9: the degree-`n` short complex attached to a filtered diagram of
cochain complexes, formed inside the functor category of module diagrams. -/
private def degree_shortComplex
    {J : Type*} [Category J]
    (G : J ⥤ CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    ShortComplex (J ⥤ ModuleCat R) :=
  ShortComplex.mk
    (prev_d_natTrans (G := G) n)
    (next_d_natTrans (G := G) n)
    (degree_d_comp_eq_zero (G := G) n)

/-- Helper for Lemma 15.59.9: evaluating the functor-category degree-`n` short complex at a
stage recovers the ordinary degree-`n` short complex of that stage. -/
private def degree_shortComplex_app_iso
    {J : Type*} [Category J]
    (G : J ⥤ CochainComplex (ModuleCat R) ℤ) (n : ℤ) (j : J) :
    (degree_shortComplex (G := G) n).map ((evaluation J (ModuleCat R)).obj j) ≅
      (G.obj j).sc n :=
  -- Both short complexes have the same terms and differentials after evaluation at `j`.
  (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)) ≪≫
    ((G.obj j).isoSc' (i := n - 1) (j := n) (k := n + 1)
      (CochainComplex.prev ℤ n) (CochainComplex.next ℤ n)).symm

/-- Helper for Lemma 15.59.9: if each stage of a filtered diagram of cochain complexes is exact at
degree `n`, then the induced degree-`n` short complex in the functor category is exact. -/
private theorem degree_shortComplex_exact
    {J : Type*} [Category J]
    (G : J ⥤ CochainComplex (ModuleCat R) ℤ)
    (hG : ∀ j : J, (G.obj j).ExactAt n) :
    (degree_shortComplex (G := G) n).Exact := by
  -- Reflect exactness through evaluation, where the short complex becomes the stagewise one.
  rw [shortComplex_exact_iff_exact_app]
  intro j
  have hExactSc : ((G.obj j).sc n).Exact := by
    exact (HomologicalComplex.exactAt_iff (G.obj j) n).mp (hG j)
  exact (ShortComplex.exact_iff_of_iso (degree_shortComplex_app_iso (G := G) n j)).mpr hExactSc

/-- Helper for Lemma 15.59.9: filtered colimits of `R`-modules are exact for any small filtered
indexing category. -/
private theorem moduleCat_hasExactFilteredColimitsOfShape
    {J : Type v} [SmallCategory J] [IsFiltered J] :
    HasExactColimitsOfShape J (ModuleCat.{v, u} R) := by
  let _ : Limits.HasColimitsOfShape J AddCommGrpCat.{v} := by
    let _ : Small.{v, v} J := inferInstance
    exact AddCommGrpCat.hasColimitsOfShape (J := J)
  let _ : Limits.HasColimitsOfShape J (ModuleCat.{v, u} R) := ModuleCat.hasColimitsOfShape R J
  let _ : AB5OfSize.{v, v} AddCommGrpCat.{v} := AB5OfSize_shrink AddCommGrpCat.{v}
  let _ : HasExactColimitsOfShape J AddCommGrpCat.{v} := by
    infer_instance
  -- Exactness descends across the forgetful functor to additive groups.
  exact HasExactColimitsOfShape.domain_of_functor J
    (forget₂ (ModuleCat.{v, u} R) AddCommGrpCat.{v})

/-- Helper for Lemma 15.59.9: the first `mapShortComplex` compatibility condition for the
degree-`n` short complex is the canonical colimit relation for the previous differential. -/
private theorem degree_shortComplex_colimit_map_prev
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (G : J ⥤ CochainComplex (ModuleCat.{v, u} R) ℤ) (n : ℤ) (j : J) :
    colimit.ι (degree_shortComplex (G := G) n).X₁ j ≫ colim.map (prev_d_natTrans (G := G) n) =
      (degree_shortComplex (G := G) n).f.app j ≫
        colimit.ι (degree_shortComplex (G := G) n).X₂ j := by
  let _ : HasColimitsOfShape J (ModuleCat.{v, u} R) := ModuleCat.hasColimitsOfShape R J
  -- This is exactly `colimit.ι_map`, after unfolding the short-complex structure morphism.
  simpa [degree_shortComplex] using (colimit.ι_map (prev_d_natTrans (G := G) n) j)

/-- Helper for Lemma 15.59.9: the second `mapShortComplex` compatibility condition for the
degree-`n` short complex is the canonical colimit relation for the next differential. -/
private theorem degree_shortComplex_colimit_map_next
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (G : J ⥤ CochainComplex (ModuleCat.{v, u} R) ℤ) (n : ℤ) (j : J) :
    colimit.ι (degree_shortComplex (G := G) n).X₂ j ≫ colim.map (next_d_natTrans (G := G) n) =
      (degree_shortComplex (G := G) n).g.app j ≫
        colimit.ι (degree_shortComplex (G := G) n).X₃ j := by
  let _ : HasColimitsOfShape J (ModuleCat.{v, u} R) := ModuleCat.hasColimitsOfShape R J
  -- This is the same `ι_map` identity for the second short-complex morphism.
  simpa [degree_shortComplex] using (colimit.ι_map (next_d_natTrans (G := G) n) j)

/-- Helper for Lemma 15.59.9: evaluating the chosen colimit cocone of `G` at degree `k` produces
the canonical cocone on the degree-`k` module diagram. -/
private def colimit_degree_term_cocone
    {J : Type v} [Category.{v} J] [IsFiltered J]
    (G : J ⥤ CochainComplex (ModuleCat.{v, u} R) ℤ) [HasColimit G] (k : ℤ) :
    Cocone (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) k) :=
  (HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) k).mapCocone (colimit.cocone G)

/-- Helper for Lemma 15.59.9: evaluation preserves the chosen colimit of `G`, so the degree-`k`
evaluated cocone is colimiting. -/
private def colimit_degree_term_isColimit
    {J : Type v} [Category.{v} J] [IsFiltered J]
    (G : J ⥤ CochainComplex (ModuleCat.{v, u} R) ℤ) [HasColimit G] (k : ℤ) :
    IsColimit (colimit_degree_term_cocone (R := R) (G := G) k) :=
  Limits.isColimitOfPreserves
    (HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) k)
    (colimit.isColimit G)

/-- Helper for Lemma 15.59.9: the colimit of the degree-`k` terms is canonically the degree-`k`
term of the colimit complex. -/
private noncomputable def colimit_degree_term_iso
    {J : Type v} [Category.{v} J] [IsFiltered J]
    (G : J ⥤ CochainComplex (ModuleCat.{v, u} R) ℤ) [HasColimit G] (k : ℤ) :
    colimit (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) k) ≅
      (colimit G).X k :=
  ((colimit_degree_term_isColimit (R := R) (G := G) k).coconePointUniqueUpToIso
    (colimit.isColimit
      (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) k))).symm

/-- Helper for Lemma 15.59.9: on each cocone leg, the degreewise colimit comparison is the
canonical degree-`k` map into the colimit complex. -/
private theorem colimit_degree_term_iso_hom_ι
    {J : Type v} [Category.{v} J] [IsFiltered J]
    (G : J ⥤ CochainComplex (ModuleCat.{v, u} R) ℤ) [HasColimit G] (k : ℤ) (j : J) :
    colimit.ι
        (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) k) j ≫
          (colimit_degree_term_iso (R := R) (G := G) k).hom =
      (colimit.ι G j).f k := by
  let e :
      (colimit G).X k ≅
        colimit (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) k) :=
    (colimit_degree_term_isColimit (R := R) (G := G) k).coconePointUniqueUpToIso
      (colimit.isColimit
        (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) k))
  have h :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit_degree_term_isColimit (R := R) (G := G) k)
      (colimit.isColimit
        (G ⋙ HomologicalComplex.eval (ModuleCat.{v, u} R) (ComplexShape.up ℤ) k)) j
  -- Compose the cocone-leg identity with the inverse comparison to obtain the chosen direction.
  simpa [colimit_degree_term_iso, colimit_degree_term_cocone, e] using
    (congrArg (fun f ↦ f ≫ e.inv) h).symm

/-- Helper for Lemma 15.59.9: the degreewise colimit comparison intertwines the previous
differential with the colimit of the previous-differential natural transformation. -/
private theorem colimit_degree_term_iso_prev_comm
    {J : Type v} [Category.{v} J] [IsFiltered J]
    (G : J ⥤ CochainComplex (ModuleCat.{v, u} R) ℤ) [HasColimit G] (n : ℤ) :
    (colimit_degree_term_iso (R := R) (G := G) (n - 1)).hom ≫ (colimit G).d (n - 1) n =
      colim.map (prev_d_natTrans (G := G) n) ≫
        (colimit_degree_term_iso (R := R) (G := G) n).hom := by
  -- TODO: reprove the cocone-leg comparison after normalizing the reassociation shape expected by
  -- `calc`; the current proof route is structurally correct but needs a stable `Category.assoc`
  -- normalization for the colimit comparison morphisms.
  sorry

/-- Helper for Lemma 15.59.9: the degreewise colimit comparison intertwines the next
differential with the colimit of the next-differential natural transformation. -/
private theorem colimit_degree_term_iso_next_comm
    {J : Type v} [Category.{v} J] [IsFiltered J]
    (G : J ⥤ CochainComplex (ModuleCat.{v, u} R) ℤ) [HasColimit G] (n : ℤ) :
    (colimit_degree_term_iso (R := R) (G := G) n).hom ≫ (colimit G).d n (n + 1) =
      colim.map (next_d_natTrans (G := G) n) ≫
        (colimit_degree_term_iso (R := R) (G := G) (n + 1)).hom := by
  -- TODO: reprove the forward differential comparison after the same reassociation cleanup as in
  -- `colimit_degree_term_iso_prev_comm`.
  sorry

/-- Helper for Lemma 15.59.9: the canonical colimit short complex of `degree_shortComplex G n`
identifies with the degree-`n` short complex of the colimit complex. -/
private noncomputable def colimit_degree_shortComplex_iso
    {J : Type v} [Category.{v} J] [IsFiltered J]
    (G : J ⥤ CochainComplex (ModuleCat.{v, u} R) ℤ) [HasColimit G] (n : ℤ) :
    colim.mapShortComplex (degree_shortComplex (G := G) n)
      (colimit.isColimit _)
      (colimit.cocone _)
      (colimit.cocone _)
      (colim.map (prev_d_natTrans (G := G) n))
      (colim.map (next_d_natTrans (G := G) n))
      (degree_shortComplex_colimit_map_prev (G := G) n)
      (degree_shortComplex_colimit_map_next (G := G) n) ≅
        (colimit G).sc n :=
  -- TODO: once the two degreewise colimit/differential comparison lemmas are restabilized, this
  -- short-complex isomorphism is rebuilt from those three component isomorphisms exactly as in the
  -- current source-faithful route.
  sorry

/-- Helper for Lemma 15.59.9: exactness descends from a filtered short-complex diagram of modules
to the short complex obtained on colimits. -/
private theorem colimit_mapShortComplex_exact_of_isFiltered
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (S : ShortComplex (J ⥤ ModuleCat.{v, u} R)) (hS : S.Exact) :
    (colim.mapShortComplex S
      (colimit.isColimit S.X₁)
      (colimit.cocone S.X₂)
      (colimit.cocone S.X₃)
      (colim.map S.f)
      (colim.map S.g)
      (fun j ↦ by simp)
      (fun j ↦ by simp)).Exact := by
  -- Exact filtered colimits are already available in `ModuleCat R`, so use the canonical owner
  -- theorem on `mapShortComplex`.
  let _ : HasExactColimitsOfShape J (ModuleCat.{v, u} R) :=
    moduleCat_hasExactFilteredColimitsOfShape (R := R) (J := J)
  exact Limits.colim.exact_mapShortComplex hS
    (colimit.isColimit S.X₁)
    (colimit.isColimit S.X₂)
    (colimit.isColimit S.X₃)
    (colim.map S.f)
    (colim.map S.g)
    (fun j ↦ by simp)
    (fun j ↦ by simp)

/-- Helper for Lemma 15.59.9: specialize exactness of filtered colimits to the explicit
degree-`n` short complex attached to a filtered diagram of cochain complexes. -/
private theorem colimit_degree_shortComplex_exact_of_isFiltered
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (G : J ⥤ CochainComplex (ModuleCat.{v, u} R) ℤ)
    (n : ℤ)
    (hG : ∀ j : J, (G.obj j).ExactAt n) :
    (colim.mapShortComplex (degree_shortComplex (G := G) n)
      (colimit.isColimit _)
      (colimit.cocone _)
      (colimit.cocone _)
      (colim.map (prev_d_natTrans (G := G) n))
      (colim.map (next_d_natTrans (G := G) n))
      (degree_shortComplex_colimit_map_prev (G := G) n)
      (degree_shortComplex_colimit_map_next (G := G) n)).Exact := by
  -- TODO: after the explicit `mapShortComplex` surface is restated in the exact shape expected by
  -- `colim.mapShortComplex`, this is the filtered-exactness transport from
  -- `colimit_mapShortComplex_exact_of_isFiltered`.
  sorry

/-- Helper for Lemma 15.59.9: if a filtered diagram of cochain complexes is exact at degree `n`
stagewise, then its colimit complex is exact at degree `n`. -/
private theorem colimit_exactAt_of_isFiltered
    {J : Type*} [SmallCategory J] [IsFiltered J]
    (G : J ⥤ CochainComplex (ModuleCat R) ℤ)
    (n : ℤ)
    (hG : ∀ j : J, (G.obj j).ExactAt n) :
    (colimit G).ExactAt n := by
  -- TODO: package the exactness transfer entirely through the stabilized `colim.mapShortComplex`
  -- surface once the two colimit-comparison equalities and the `mapShortComplex` shape agree.
  sorry

/-- Helper for Lemma 15.59.9: Lemma `10.11.3` can be unpacked into an explicit filtered-colimit
presentation of a module by finitely presented modules. -/
lemma exists_filtered_presentation_by_finitelyPresented_modules
    (M : ModuleCat R) :
    ∃ (J : Type _) (_ : SmallCategory J) (_ : IsFiltered J)
      (pres : ColimitPresentation J M), ∀ j : J, Module.FinitePresentation R (pres.diag.obj j) := by
  -- Unfold the owner `ObjectProperty.ind` once so the later tensor-colimit argument can work with
  -- an actual filtered diagram and its colimit presentation.
  simpa [CategoryTheory.ObjectProperty.ind] using
    (module_is_isomorphic_to_colimit_of_directed_system_of_finitelyPresented (R := R) (M := M))

/-- Helper for Lemma 15.59.9: after first taking the colimit through `single₀` and then through
tensoring on the left by `K`, the colimit diagram identifies with tensoring `K` against the
degree-zero single complex on the presented module. -/
private noncomputable def tensor_single_zero_colimit_iso
    {J : Type*} [SmallCategory J] [IsFiltered J]
    {M : ModuleCat R} (pres : ColimitPresentation J M)
    (K : CochainComplex (ModuleCat R) ℤ)
    [HasColimit (pres.diag ⋙ single₀ ⋙ MonoidalCategory.tensorLeft K)] :
    colimit (pres.diag ⋙ single₀ ⋙ MonoidalCategory.tensorLeft K) ≅
      HomologicalComplex.tensorObj K ((single₀).obj M) :=
  -- TODO: rebuild the explicit two-step colimit presentation using the colimit-preservation API
  -- from Lemma `10.12.9`; the current term failed because the required `single₀` colimit
  -- preservation instance is not being inferred on this surface.
  sorry

/-- Helper for Lemma 15.59.9: shifting the degree-`n` single complex by `n` identifies it with
the degree-zero single complex. -/
private theorem single_shift_to_zero_eq
    (n : ℤ) :
    n + 0 = n := by
  -- This is the index equality required by `singleFunctors.shiftIso`.
  simp

/-- Helper for Lemma 15.59.9: a single cochain complex shifted by its own degree is the
corresponding degree-zero single complex. -/
private noncomputable def single_shift_to_zero_iso
    (M : ModuleCat R) (n : ℤ) :
    (((singleFunctor (ModuleCat R) n).obj M)⟦n⟧) ≅
      ((single₀).obj M) :=
  ((CochainComplex.singleFunctors (ModuleCat R)).shiftIso n 0 n
    (single_shift_to_zero_eq n)).app M

/-- Helper for Lemma 15.59.9: after unpacking the filtered presentation of `M`, the source proof
reduces the degree-zero all-modules claim to one fixed-degree exactness statement. -/
lemma tensor_single_zero_exactAt_of_module
    (K : CochainComplex (ModuleCat R) ℤ)
    (hfp : ∀ (M : ModuleCat R) [Module.FinitePresentation R M],
      (HomologicalComplex.tensorObj K ((single₀).obj M)).Acyclic)
    (M : ModuleCat R) (n : ℤ) :
    (HomologicalComplex.tensorObj K ((single₀).obj M)).ExactAt n := by
  -- Route correction: isolate the source proof degreewise before reassembling acyclicity, so the
  -- remaining blocker is exactly the filtered-colimit comparison for one short complex.
  rcases exists_filtered_presentation_by_finitelyPresented_modules (R := R) M with
    ⟨J, _, _, pres, hpres⟩
  let F : J ⥤ ModuleCat R := pres.diag
  let G : J ⥤ CochainComplex (ModuleCat R) ℤ :=
    F ⋙ single₀ ⋙ MonoidalCategory.tensorLeft K
  have hstage :
      ∀ j : J, (G.obj j).ExactAt n := by
    intro j
    -- Each stage of the chosen presentation is finitely presented, so the original hypothesis
    -- already gives exactness after tensoring with that degree-zero single complex.
    letI := hpres j
    simpa [G, F] using
      tensor_single_zero_exactAt_of_finitePresentation (K := K) hfp (F.obj j) n
  have hColim : (colimit G).ExactAt n :=
    colimit_exactAt_of_isFiltered (R := R) G n hstage
  let eTensor :
      colimit G ≅ HomologicalComplex.tensorObj K ((single₀).obj M) :=
    tensor_single_zero_colimit_iso (R := R) pres K
  -- The degreewise exactness of the filtered colimit now transfers across the explicit two-step
  -- colimit comparison for `single₀` followed by `tensorLeft K`.
  exact HomologicalComplex.ExactAt.of_iso hColim eTensor

/-- Helper for Lemma 15.59.9: extend the degree-zero tensor test from finitely presented modules
to arbitrary modules using the filtered-colimit presentation from Lemma `10.11.3`. -/
lemma tensor_single_zero_acyclic_of_module
    (K : CochainComplex (ModuleCat R) ℤ)
    (hfp : ∀ (M : ModuleCat R) [Module.FinitePresentation R M],
      (HomologicalComplex.tensorObj K ((single₀).obj M)).Acyclic)
    (M : ModuleCat R) :
    (HomologicalComplex.tensorObj K ((single₀).obj M)).Acyclic := by
  -- Reassemble acyclicity from the degreewise exactness statement isolated above.
  rw [HomologicalComplex.acyclic_iff]
  intro n
  exact tensor_single_zero_exactAt_of_module (K := K) hfp M n

/-- Helper for Lemma 15.59.9: swap the two tensor inputs on cochain complexes once, so the
downstream brutal-left proof can use a named owner instead of repeating the braiding interface. -/
noncomputable def tensor_swap_iso
    (K L : CochainComplex (ModuleCat R) ℤ) :
    HomologicalComplex.tensorObj K L ≅ HomologicalComplex.tensorObj L K :=
  -- The symmetric monoidal braiding on cochain complexes is exactly the required tensor swap.
  β_ K L

/-- Helper for Lemma 15.59.9: fixed-right tensoring commutes with cochain shifts via the canonical
first-variable shift comparison for the tensor bifunctor. -/
noncomputable def tensor_right_shift_transport_iso
    (K L : CochainComplex (ModuleCat R) ℤ) (b : ℤ) :
    HomologicalComplex.tensorObj (L⟦b⟧) K ≅
      (HomologicalComplex.tensorObj L K)⟦b⟧ := by
  -- Route correction: use the tensor-bifunctor shift owner directly instead of the functor-level
  -- `commShiftIso`, which was the unstable transport surface in earlier attempts.
  simpa using
    (CochainComplex.mapBifunctorShift₁Iso L K (curriedTensor (ModuleCat R)) b)

/-- Helper for Lemma 15.59.9: shift the degree-zero all-modules tensor test to arbitrary
single-term complexes. -/
lemma tensor_single_acyclic_of_module
    (K : CochainComplex (ModuleCat R) ℤ)
    (hfp : ∀ (M : ModuleCat R) [Module.FinitePresentation R M],
      (HomologicalComplex.tensorObj K ((single₀).obj M)).Acyclic)
    (n : ℤ) (M : ModuleCat R) :
    (HomologicalComplex.tensorObj K ((singleFunctor (ModuleCat R) n).obj M)).Acyclic := by
  let eSingle :
      (((singleFunctor (ModuleCat R) n).obj M)⟦n⟧) ≅
        ((single₀).obj M) :=
    single_shift_to_zero_iso (M := M) n
  have hZero :
      (HomologicalComplex.tensorObj K ((single₀).obj M)).Acyclic :=
    tensor_single_zero_acyclic_of_module (K := K) hfp M
  have hShiftedSingle :
      (HomologicalComplex.tensorObj K (((singleFunctor (ModuleCat R) n).obj M)⟦n⟧)).Acyclic := by
    let eTensor :
        HomologicalComplex.tensorObj K (((singleFunctor (ModuleCat R) n).obj M)⟦n⟧) ≅
          HomologicalComplex.tensorObj K ((single₀).obj M) :=
      (MonoidalCategory.tensorLeft K).mapIso eSingle
    -- First rewrite the shifted single complex to degree `0`.
    exact acyclic_of_iso (R := R) eTensor.symm hZero
  have hTensorShifted :
      ((HomologicalComplex.tensorObj K ((singleFunctor (ModuleCat R) n).obj M))⟦n⟧).Acyclic := by
    -- Then commute the fixed-left tensor product across the shift in the right variable.
    exact acyclic_of_iso (R := R)
      (CochainComplex.mapBifunctorShift₂Iso K ((singleFunctor (ModuleCat R) n).obj M)
        (curriedTensor (ModuleCat R)) n)
      hShiftedSingle
  -- Finally descend acyclicity from the shifted tensor complex back to the original one.
  exact acyclic_of_shift (R := R)
    (HomologicalComplex.tensorObj K ((singleFunctor (ModuleCat R) n).obj M)) n
    hTensorShifted

/-- Helper for Lemma 15.59.9: the right-oriented single-complex tensor test immediately gives the
left-oriented form used in the brutal-left truncation argument. -/
lemma tensor_single_left_acyclic_of_module
    (K : CochainComplex (ModuleCat R) ℤ)
    (hfp : ∀ (M : ModuleCat R) [Module.FinitePresentation R M],
      (HomologicalComplex.tensorObj K ((single₀).obj M)).Acyclic)
    (n : ℤ) (M : ModuleCat R) :
    (HomologicalComplex.tensorObj ((singleFunctor (ModuleCat R) n).obj M) K).Acyclic := by
  let eBraiding :
      HomologicalComplex.tensorObj ((singleFunctor (ModuleCat R) n).obj M) K ≅
        HomologicalComplex.tensorObj K ((singleFunctor (ModuleCat R) n).obj M) :=
    tensor_swap_iso ((singleFunctor (ModuleCat R) n).obj M) K
  have hRight :
      (HomologicalComplex.tensorObj K ((singleFunctor (ModuleCat R) n).obj M)).Acyclic :=
    tensor_single_acyclic_of_module (K := K) hfp n M
  -- The braiding isomorphism is the only interface change needed before starting the source
  -- brutal-left induction on bounded-above test complexes.
  exact acyclic_of_iso (R := R) eBraiding.symm hRight

/-- Helper for Lemma 15.59.9: every upper truncation of an acyclic complex is again acyclic. -/
lemma truncLE_acyclic_of_acyclic
    {L : CochainComplex (ModuleCat R) ℤ}
    (hL : L.Acyclic) (b : ℤ) :
    (L.truncLE b).Acyclic := by
  -- Route correction: transfer exactness through the canonical quasi-isomorphism
  -- `L.truncLE b ⟶ L` instead of unfolding the truncation differential.
  rw [HomologicalComplex.acyclic_iff] at hL ⊢
  have hLE : L.IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro n hn
    -- Acyclicity forces vanishing homology in every degree, so any upper bound works.
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (by
      rw [← HomologicalComplex.exactAt_iff_isZero_homology]
      exact hL n)
  letI : L.IsLE b := hLE
  intro n
  -- Exactness pulls back along the quasi-isomorphism `L.ιTruncLE b`.
  exact (exactAt_iff_of_quasiIsoAt (L.ιTruncLE b) n).2 (hL n)

/-- Helper for Lemma 15.59.9: a boundary produced after upper truncation pushes forward to a
boundary in the original tensor complex. -/
lemma tensor_boundary_descends_from_truncLE
    (K : CochainComplex (ModuleCat R) ℤ)
    {L : CochainComplex (ModuleCat R) ℤ} [_h : HomologicalComplex.HasTensor L K]
    (n b : ℤ)
    {z' : (HomologicalComplex.tensorObj (L.truncLE b) K).X n}
    {z : (HomologicalComplex.tensorObj L K).X n}
    (hz : (((HomologicalComplex.tensorHom (L.ιTruncLE b) (𝟙 K)).f n).hom z' = z))
    (hb :
      ∃ y' : (HomologicalComplex.tensorObj (L.truncLE b) K).X (n - 1),
        ((HomologicalComplex.tensorObj (L.truncLE b) K).d (n - 1) n).hom y' = z') :
    ∃ y : (HomologicalComplex.tensorObj L K).X (n - 1),
      ((HomologicalComplex.tensorObj L K).d (n - 1) n).hom y = z := by
  rcases hb with ⟨y', hy'⟩
  refine ⟨((HomologicalComplex.tensorHom (L.ιTruncLE b) (𝟙 K)).f (n - 1)).hom y', ?_⟩
  -- Apply the degree-`n - 1 → n` naturality square for `tensorHom`.
  have hcomm :=
    (HomologicalComplex.tensorHom (L.ιTruncLE b) (𝟙 K)).comm (n - 1) n
  have hcomm_apply :
      (((HomologicalComplex.tensorHom (L.ιTruncLE b) (𝟙 K)).f (n - 1) ≫
          (HomologicalComplex.tensorObj L K).d (n - 1) n).hom y') =
        (((HomologicalComplex.tensorObj (L.truncLE b) K).d (n - 1) n ≫
          (HomologicalComplex.tensorHom (L.ιTruncLE b) (𝟙 K)).f n).hom y') := by
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hcomm) y'
  -- After evaluating the commutative square on `y'`, both sides become the required boundary.
  change
    (((HomologicalComplex.tensorHom (L.ιTruncLE b) (𝟙 K)).f (n - 1) ≫
        (HomologicalComplex.tensorObj L K).d (n - 1) n).hom y') = z
  calc
    (((HomologicalComplex.tensorHom (L.ιTruncLE b) (𝟙 K)).f (n - 1) ≫
        (HomologicalComplex.tensorObj L K).d (n - 1) n).hom y')
      = (((HomologicalComplex.tensorObj (L.truncLE b) K).d (n - 1) n ≫
            (HomologicalComplex.tensorHom (L.ιTruncLE b) (𝟙 K)).f n).hom y') := hcomm_apply
    _ = ((HomologicalComplex.tensorHom (L.ιTruncLE b) (𝟙 K)).f n).hom
          (((HomologicalComplex.tensorObj (L.truncLE b) K).d (n - 1) n).hom y') := rfl
    _ = ((HomologicalComplex.tensorHom (L.ιTruncLE b) (𝟙 K)).f n).hom z' := by rw [hy']
    _ = z := hz

/-- Helper for Lemma 15.59.9: once the tensor test is known for every single-term module complex,
bounded-above acyclic complexes with cutoff `0` tensor to acyclic complexes. -/
lemma tensor_boundedAbove_acyclic_of_all_modules_zero
    (K : CochainComplex (ModuleCat R) ℤ)
    (hsingleLeft : ∀ (n : ℤ) (M : ModuleCat R),
      (HomologicalComplex.tensorObj ((singleFunctor (ModuleCat R) n).obj M) K).Acyclic)
    {Q : CochainComplex (ModuleCat R) ℤ} [Q.IsStrictlyLE 0]
    (hQ : Q.Acyclic) :
    (HomologicalComplex.tensorObj Q K).Acyclic := by
  -- Route correction: isolate the source zero-cutoff brutal-left/Postnikov argument as the only
  -- remaining bounded-above blocker, so the public theorem below is just shift normalization.
  -- TODO: prove finite-stage acyclicity for `shifted_brutal_left_stage Q m` using
  -- `shifted_brutal_left_stage_short_exact_sign_corrected` and
  -- `shifted_brutal_single_shift_back_iso`, pass exactness to the sequential colimit by
  -- `colimit_exactAt_of_isFiltered`, and transport across
  -- `CategoryTheory.brutalLeftTruncationColimitComparison_isIso`.
  sorry

/-- Helper for Lemma 15.59.9: once the tensor test is known for every single-term module complex,
bounded-above acyclic complexes tensor to acyclic complexes. -/
lemma tensor_boundedAbove_acyclic_of_all_modules
    (K : CochainComplex (ModuleCat R) ℤ)
    (hsingleLeft : ∀ (n : ℤ) (M : ModuleCat R),
      (HomologicalComplex.tensorObj ((singleFunctor (ModuleCat R) n).obj M) K).Acyclic)
    {L : CochainComplex (ModuleCat R) ℤ} (b : ℤ)
    (hL : L.Acyclic) [L.IsStrictlyLE b] :
    (HomologicalComplex.tensorObj L K).Acyclic := by
  -- Route correction: normalize to the zero-cutoff case by shifting `L` to `L⟦b⟧`, then descend
  -- back along the canonical tensor/shift comparison isomorphism.
  have hShiftLE : (L⟦b⟧).IsStrictlyLE 0 := by
    -- Shifting the support interval by `b` moves the upper bound from `b` down to `0`.
    simpa using L.isStrictlyLE_shift b b 0 (by omega)
  letI : (L⟦b⟧).IsStrictlyLE 0 := hShiftLE
  have hShiftAcyclic : (L⟦b⟧).Acyclic := by
    -- Acyclicity is invariant under cochain shifts.
    exact acyclic_shift (R := R) L b hL
  have hTensorShiftAcyclic :
      (HomologicalComplex.tensorObj (L⟦b⟧) K).Acyclic := by
    -- Apply the zero-cutoff bounded-above theorem to the shifted complex.
    exact tensor_boundedAbove_acyclic_of_all_modules_zero (K := K) hsingleLeft hShiftAcyclic
  have hTensorShifted :
      ((HomologicalComplex.tensorObj L K)⟦b⟧).Acyclic := by
    -- Rewrite the shifted tensor complex using the fixed-right tensor/shift comparison.
    exact acyclic_of_iso (R := R)
      (tensor_right_shift_transport_iso (K := K) (L := L) b) hTensorShiftAcyclic
  -- Descend acyclicity from the shifted tensor complex back to the original tensor complex.
  exact acyclic_of_shift (R := R) (HomologicalComplex.tensorObj L K) b hTensorShifted

/-- Helper for Lemma 15.59.9: reduce an arbitrary acyclic test complex to bounded-above
truncations. -/
lemma tensor_acyclic_of_acyclic
    (K : CochainComplex (ModuleCat R) ℤ)
    (hsingleLeft : ∀ (n : ℤ) (M : ModuleCat R),
      (HomologicalComplex.tensorObj ((singleFunctor (ModuleCat R) n).obj M) K).Acyclic)
    {L : CochainComplex (ModuleCat R) ℤ} [_h : HomologicalComplex.HasTensor L K]
    (hL : L.Acyclic) :
    (HomologicalComplex.tensorObj L K).Acyclic := by
  rw [HomologicalComplex.acyclic_iff]
  intro n
  have hTrunc :
      ∀ b : ℤ, (L.truncLE b).Acyclic :=
    truncLE_acyclic_of_acyclic (L := L) hL
  have hTruncTensor :
      ∀ b : ℤ, (HomologicalComplex.tensorObj (L.truncLE b) K).Acyclic := by
    intro b
    -- Each upper truncation is bounded above, so the bounded-above tensor lemma applies once the
    -- cycle has been pushed into that truncation.
    exact tensor_boundedAbove_acyclic_of_all_modules (K := K) hsingleLeft b (hTrunc b)
  -- The final source step is an elementwise truncation argument: every cycle and every boundary
  -- witness in the tensor totalization is supported in some upper truncation `L.truncLE b`.
  -- TODO: prove the cycle-support factorization lemma through some `L.truncLE b`, kill the lifted
  -- cycle using `(hTruncTensor b).ExactAt n`, and then push the resulting boundary back down with
  -- `tensor_boundary_descends_from_truncLE`.
  sorry

-- Proof sketch: by Lemmas `10.11.3` and `10.12.9`, the same tensor-acyclicity holds for every
-- `R`-module because every module is a filtered colimit of finitely presented modules. Then
-- truncate an arbitrary acyclic complex termwise, use exactness of filtered colimits to reduce to
-- bounded complexes, and finish by induction on the length of the bounded complex via
-- Lemma `15.58.4` and the two-out-of-three argument from Lemma `15.59.6`.
/-- Lemma 15.59.9: if tensoring a cochain complex `K^•` of `R`-modules on the right with every
finitely presented `R`-module gives an acyclic cochain complex, then `K^•` is K-flat. -/
theorem isKFlat_of_tensor_finitelyPresented_acyclic
    (K : CochainComplex (ModuleCat R) ℤ)
    (hfp : ∀ (M : ModuleCat R) [Module.FinitePresentation R M],
      (HomologicalComplex.tensorObj K ((single₀).obj M)).Acyclic) :
    K.IsKFlat := by
  -- Route correction: keep the source-faithful global architecture explicit in the main theorem.
  -- First upgrade the degree-zero tensor test to all modules, then shift to all single complexes,
  -- and finally reduce an arbitrary acyclic test complex by bounded-above truncations.
  rw [CochainComplex.isKFlat_iff]
  intro L _ hL
  have hsingleLeft :
      ∀ (n : ℤ) (M : ModuleCat R),
        (HomologicalComplex.tensorObj ((singleFunctor (ModuleCat R) n).obj M) K).Acyclic := by
    intro n M
    -- The bounded-above source argument is written with single complexes on the left, so first
    -- pass from the degree-zero test to the right-oriented single-complex statement and then
    -- swap the tensor factors by braiding.
    exact tensor_single_left_acyclic_of_module (K := K) hfp n M
  -- The remaining proof is the truncation reduction from an arbitrary acyclic complex to the
  -- bounded-above case.
  exact tensor_acyclic_of_acyclic (K := K) hsingleLeft hL

end CochainComplex
