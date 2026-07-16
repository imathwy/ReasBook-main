import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Module.FinitePresentation
import StacksProject_2024.stacks_project.Chap15.Definition_15_65_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open DerivedCategory
open CochainComplex.HomComplex.Cocycle
open CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/- Domain-style sampling for Lemma 15.66.6:
- primary domain: pseudo-coherent objects in a derived category and the degree-`i` homology map
  induced by a morphism into an object concentrated in degree `i`;
- sampled owner declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `DerivedCategory.homologyFunctor`,
  `DerivedCategory.singleFunctor`,
  `singleFunctorCompHomologyFunctorIso`;
- best owner abstraction: the source-facing content is the existence theorem below; the canonical
  owners are pseudo-coherence, homology, and single-degree objects in `DerivedCategory`. The map
  `H^i(K) ⟶ M` induced by `α : K ⟶ M[-i]` is bridge/view data obtained directly from the owner
  comparison `singleFunctorCompHomologyFunctorIso`; the reusable bridge is exposed below as
  `DerivedCategory.homologyToSingle`, and the source-facing theorem should use that bridge rather
  than repeat the raw composite;
- primitive vs. derived:
  primitive data are `K`, `M`, and the morphism
  `α : K ⟶ (DerivedCategory.singleFunctor (ModuleCat R) i).obj M`;
  derived API is the induced homology comparison `homologyToSingle i α`.
- source/core/bridge triage:
  `source-facing`: the existence theorem `exists_finitelyPresented_module_map_inducing_mono_of_isPseudoCoherent`;
  `core/canonical`: `K.IsPseudoCoherent`, `homologyFunctor`, `singleFunctor`, and
    `singleFunctorCompHomologyFunctorIso`;
  `bridge/view`: `DerivedCategory.homologyToSingle`.
-/

section

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single" => DerivedCategory.singleFunctor (ModuleCat R)

namespace DerivedCategory

/-- The canonical map `H^i(K) ⟶ M` induced by a morphism `K ⟶ M[-i]`, expressed via the owner
comparison `singleFunctorCompHomologyFunctorIso`. -/
abbrev homologyToSingle {K : DMod} {M : ModuleCat R} (i : ℤ)
    (α : K ⟶ (single i).obj M) : (H i).obj K ⟶ M :=
  (H i).map α ≫ ((singleFunctorCompHomologyFunctorIso (ModuleCat R) i).app M).hom

end DerivedCategory

/-- Helper for Lemma 15.66.6: the module chosen from a representative is the cokernel of the
previous differential. -/
noncomputable abbrev differentialCokernel
    {E : Cpx} (i : ℤ) : ModuleCat R :=
  CategoryTheory.Limits.cokernel (E.d (i - 1) i)

/-- Helper for Lemma 15.66.6: the cokernel of the differential
`E.d (i - 1) i : E.X (i - 1) ⟶ E.X i` is finitely presented when `E` is termwise finite free. -/
lemma differential_cokernel_finitePresentation
    {E : Cpx} [E.IsTermwiseFiniteFree] (i : ℤ) :
    Module.FinitePresentation R (differentialCokernel (R := R) (E := E) i) := by
  -- Replace the categorical cokernel by the quotient by the image, where finite presentation is a
  -- standard quotient-of-finitely-presented argument.
  letI : Module.FinitePresentation R (E.X i) :=
    Module.finitePresentation_of_projective R (E.X i)
  have hfg :
      (LinearMap.ker (LinearMap.range (E.d (i - 1) i).hom).mkQ).FG := by
    simpa [Submodule.ker_mkQ] using Submodule.fg_range (E.d (i - 1) i).hom
  letI : Module.FinitePresentation R ((E.X i) ⧸ LinearMap.range (E.d (i - 1) i).hom) :=
    Module.finitePresentation_of_surjective
      (LinearMap.range (E.d (i - 1) i).hom).mkQ
      (LinearMap.range (E.d (i - 1) i).hom).mkQ_surjective
      hfg
  exact
    Module.FinitePresentation.of_equiv
      (ModuleCat.cokernelIsoRangeQuotient (E.d (i - 1) i)).symm.toLinearEquiv

/-- Helper for Lemma 15.66.6: the quotient map kills the previous differential. -/
lemma differential_comp_cokernel_π_eq_zero
    {E : Cpx} (i : ℤ) :
    E.d (i - 1) i ≫ CategoryTheory.Limits.cokernel.π (E.d (i - 1) i) = 0 := by
  exact CategoryTheory.Limits.cokernel.condition (E.d (i - 1) i)

/-- Helper for Lemma 15.66.6: the degree equation `i + 0 = i` for the `toSingleMk` constructor. -/
lemma add_zero_eq_self_int (i : ℤ) : i + 0 = i := by simp

/-- Helper for Lemma 15.66.6: the predecessor equation `(i - 1) + 1 = i`. -/
lemma sub_one_add_one_eq_int (i : ℤ) : i - 1 + 1 = i := by omega

/-- Helper for Lemma 15.66.6: the differential cokernel gives a canonical cochain map to the
single complex in degree `i`. -/
noncomputable def to_single_of_differential_cokernel
    {E : Cpx} (i : ℤ) :
    E ⟶ (CochainComplex.singleFunctor (ModuleCat R) i).obj
      (differentialCokernel (R := R) (E := E) i) :=
  let π := CategoryTheory.Limits.cokernel.π (E.d (i - 1) i)
  let z :=
    CochainComplex.HomComplex.Cocycle.toSingleMk
      π
      (add_zero_eq_self_int i)
      (i - 1)
      (sub_one_add_one_eq_int i)
      (differential_comp_cokernel_π_eq_zero (R := R) (E := E) i)
  z.homOf

/-- Helper for Lemma 15.66.6: the map on degree-`i` homology induced by the cokernel projection is
monic, because a cocycle mapping to zero is a boundary up to the cokernel universal property. -/
lemma homologyMap_to_single_of_differential_cokernel_mono
    {E : Cpx} (i : ℤ) :
    Mono (E.homologyMap (to_single_of_differential_cokernel (R := R) (E := E) i) i) := by
  let β := to_single_of_differential_cokernel (R := R) (E := E) i
  change Mono
    (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) i).map β))
  rw [ShortComplex.mono_homologyMap_iff_up_to_refinements]
  intro A x₂ hx₂ y₁ hxy
  -- In the target single complex, the previous differential is zero, so the hypothesis says
  -- exactly that `x₂` is killed by the cokernel projection.
  have hzero' : x₂ ≫ (to_single_of_differential_cokernel (R := R) (E := E) i).f i = 0 := by
    simpa [β] using hxy
  have hzero : x₂ ≫ CategoryTheory.Limits.cokernel.π (E.d (i - 1) i) = 0 := by
    apply (cancel_mono
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.up ℤ) i (differentialCokernel (R := R) (E := E) i)).inv).1
    simpa [to_single_of_differential_cokernel] using hzero'
  -- The cokernel universal property now produces the required local factorization through the
  -- previous differential.
  obtain ⟨A', π, hπ, x₁, hx₁⟩ :=
    (Limits.CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements
      (CategoryTheory.Limits.cokernelIsCokernel (f := E.d (i - 1) i)) x₂).mp hzero
  refine ⟨A', π, hπ, ?_, ?_⟩
  · simpa using x₁
  · simpa using hx₁

/-- Helper for Lemma 15.66.6: composing with a map into a single object rewrites `homologyToSingle`
as functoriality on homology followed by the target map's own `homologyToSingle`. -/
lemma homologyToSingle_comp
    {K L : DMod} {M : ModuleCat R} (i : ℤ)
    (f : K ⟶ L) (g : L ⟶ (single i).obj M) :
    homologyToSingle (R := R) i (f ≫ g) =
      (H i).map f ≫ homologyToSingle (R := R) i g := by
  simp [DerivedCategory.homologyToSingle, Functor.map_comp, Category.assoc]

/-- Helper for Lemma 15.66.6: on the chosen cochain representative, `homologyToSingle` unfolds to
the canonical derived comparison from homology to the target single object. -/
lemma homologyToSingle_Q_map_to_single_of_differential_cokernel
    {E : Cpx} (i : ℤ) :
    homologyToSingle (R := R) i
        (DerivedCategory.Q.map
          (to_single_of_differential_cokernel (R := R) (E := E) i)) =
      (H i).map
          (DerivedCategory.Q.map
            (to_single_of_differential_cokernel (R := R) (E := E) i)) ≫
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) i).app
          (differentialCokernel (R := R) (E := E) i)).hom := by
  -- This is exactly the definition of `homologyToSingle`.
  rfl

/-- Helper for Lemma 15.66.6: after passing from the cochain representative to the derived
category, the induced map on degree-`i` homology is still monic. -/
lemma homologyFunctor_map_Q_to_single_of_differential_cokernel_mono
    {E : Cpx} (i : ℤ) :
    Mono ((H i).map
      (DerivedCategory.Q.map
        (to_single_of_differential_cokernel (R := R) (E := E) i))) := by
  let β := to_single_of_differential_cokernel (R := R) (E := E) i
  let M := differentialCokernel (R := R) (E := E) i
  let η := DerivedCategory.homologyFunctorFactors (ModuleCat R) i
  let eE := η.app E
  let eM := η.app ((CochainComplex.singleFunctor (ModuleCat R) i).obj M)
  have hη :
      (H i).map (DerivedCategory.Q.map β) ≫
          eM.hom =
        eE.hom ≫ HomologicalComplex.homologyMap β i := by
    -- Naturality compares the derived homology map of `Q.map β` with the cochain-level map.
    simpa [β, M] using
      (DerivedCategory.homologyFunctorFactors_hom_naturality (C := ModuleCat R) β i)
  have hrewrite :
      (H i).map (DerivedCategory.Q.map β) =
        eE.hom ≫ HomologicalComplex.homologyMap β i ≫ eM.inv := by
    -- Move the target comparison isomorphism to the right-hand side to isolate the mono factor.
    apply (cancel_mono eM.hom).1
    simpa [Category.assoc] using hη
  have hmonoβ : Mono (HomologicalComplex.homologyMap β i) := by
    simpa [β] using
      (homologyMap_to_single_of_differential_cokernel_mono (R := R) (E := E) i)
  have hmono_left : Mono (eE.hom ≫ HomologicalComplex.homologyMap β i) :=
    mono_comp' (by infer_instance) hmonoβ
  -- The displayed factorization is a composite of an isomorphism, the known mono, and another
  -- isomorphism.
  rw [hrewrite]
  have hmono_right : Mono ((eE.hom ≫ HomologicalComplex.homologyMap β i) ≫ eM.inv) :=
    mono_comp' hmono_left (by infer_instance)
  simpa [Category.assoc] using hmono_right

/-- Helper for Lemma 15.66.6: the derived-category comparison `homologyToSingle` for the chosen
representative map is monic. -/
lemma homologyToSingle_Q_map_to_single_of_differential_cokernel_mono
    {E : Cpx} (i : ℤ) :
    Mono (homologyToSingle (R := R) i
      (DerivedCategory.Q.map
        (to_single_of_differential_cokernel (R := R) (E := E) i))) := by
  let β := to_single_of_differential_cokernel (R := R) (E := E) i
  letI : Mono ((H i).map (DerivedCategory.Q.map β)) :=
    homologyFunctor_map_Q_to_single_of_differential_cokernel_mono
      (R := R) (E := E) i
  -- The final factor in `homologyToSingle` is an isomorphism, so it preserves monomorphy.
  change Mono (((H i).map (DerivedCategory.Q.map β)) ≫
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) i).app
      (differentialCokernel (R := R) (E := E) i)).hom)
  infer_instance

/-- Helper for Lemma 15.66.6: precomposing a morphism into a single object by an isomorphism on
the source preserves the monicity of the induced map on homology. -/
lemma mono_homologyToSingle_precompose_iso
    {K L : DMod} {M : ModuleCat R} (i : ℤ) (e : K ≅ L)
    (β : K ⟶ (single i).obj M)
    (hβ : Mono (homologyToSingle (R := R) i β)) :
    Mono (homologyToSingle (R := R) i (e.inv ≫ β)) := by
  letI : Mono (homologyToSingle (R := R) i β) := hβ
  -- Functoriality rewrites the new map as precomposition by `(H i).map e.inv`, which is an
  -- isomorphism because `e.inv` is one.
  rw [homologyToSingle_comp]
  infer_instance

-- Proof sketch: choose a bounded-above termwise finite-free representative of `K` from
-- pseudo-coherence. Let `M` be the cokernel of the differential `P^(i - 1) ⟶ P^i`; finite
-- presentation follows because both terms are finite free. The canonical morphism from `K` to the
-- degree-`i` single object on `M` induces the natural map `H^i(K) ⟶ M`, and on the chosen
-- representative this map is the inclusion of cocycles modulo boundaries into the cokernel, hence
-- is monic.
/-- Lemma 15.66.6: if `K` is pseudo-coherent in `D(R)`, then for every `i : ℤ` there exists a
finitely presented `R`-module `M` and a morphism from `K` to the degree-`i` single object on `M`
(equivalently, to `M[-i]`) whose induced map `H^i(K) ⟶ M`, formalized as
`DerivedCategory.homologyToSingle i α`, is injective. -/
lemma exists_finitelyPresented_module_map_inducing_mono_of_isPseudoCoherent
    (K : DMod) (hK : K.IsPseudoCoherent) (i : ℤ) :
    ∃ (M : ModuleCat R) (_ : Module.FinitePresentation R M) (α : K ⟶ (single i).obj M),
      Mono (homologyToSingle i α) := by
  obtain ⟨E, _, hE, αE, hαE⟩ := hK
  let M := differentialCokernel (R := R) (E := E) i
  let β : DerivedCategory.Q.obj E ⟶ (single i).obj M :=
    DerivedCategory.Q.map (to_single_of_differential_cokernel (R := R) (E := E) i)
  letI : Module.FinitePresentation R M :=
    differential_cokernel_finitePresentation (R := R) (E := E) i
  let e : DerivedCategory.Q.obj E ≅ K := asIso αE
  refine ⟨M, inferInstance, e.inv ≫ β, ?_⟩
  -- Route correction: instead of fully normalizing the owner-level comparison inside the final
  -- theorem, transport the already-proved mono along the representative isomorphism.
  exact mono_homologyToSingle_precompose_iso
    (R := R) (i := i) e β
    (homologyToSingle_Q_map_to_single_of_differential_cokernel_mono
      (R := R) (E := E) i)

end

end CategoryTheory
