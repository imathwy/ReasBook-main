import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap13.Lemma_13_35_7
import StacksProject_2024.Chap13.Lemma_13_36_1
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import StacksProject_2024.Chap15.RingSingle
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open CategoryTheory Limits
open scoped CategoryTheory.ObjectProperty.GeneratedNotation ZeroObject

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/- Domain-style sampling for Lemma 15.80.1:
- primary domain: ghost maps in the derived category `D(R)`, detected by the canonical homology
  functor family and combined along finite chains of composable arrows;
- sampled owner declarations:
  `H^i`,
  `ComposableArrows`,
  `objectGeneratedStage_one_eq`,
  `objectGeneratedStage_succ`,
  `Triangle.yoneda_exact₂`;
- best owner abstraction: the source-facing stage condition should use the Chapter 13 owner
  `⟨ringSingle⟩_n`, the chain itself is canonically a `ComposableArrows`, and the stepwise
  vanishing mechanism is handled by reducing stage one to shifts of `R[0]`, then propagating
  through extension triangles using the exactness of represented Hom; the stage hypothesis should
  therefore be unfolded only through the canonical stage-one and successor descriptions, not
  through a new local ghost wrapper;
- primitive vs. derived:
  primitive data are the stage-membership hypothesis on the leftmost object and the degreewise
  vanishing of each arrow under all cohomology functors;
  derived API is the vanishing of the total composite, obtained by the source-faithful induction:
  first annihilate stage-one generators, then factor through the quotient term of an extension
  triangle and recurse on the tail chain.

Source/core/bridge triage:
- `source-facing`: the ghost hypothesis and the zero-composite conclusion;
- `core/canonical`: `⟨ringSingle⟩_n`, `ComposableArrows`, `H^i`,
  `Triangle.yoneda_exact₂`;
- `bridge/view`: `objectGeneratedStage_one_eq` and `objectGeneratedStage_succ`, used to pass from
  the source-facing stage hypothesis to the canonical generator/extension induction. -/

-- Proof sketch: prove the stage-one case by identifying shifts of `R[0]` with single-degree
-- objects and using that `Hom_{D(R)}(R[-i], -)` is detected by `H^i`. Then induct on the stage
-- using `objectGeneratedStage_succ`: write a stage-`(m+1)` object as an extension of a stage-one
-- object by a stage-`m` object, kill the restriction of the head ghost on the stage-one term, use
-- represented exactness to factor through the quotient, and apply the induction hypothesis to the
-- tail chain.
/-- Helper for Lemma 15.80.1: a morphism out of the middle term of a distinguished triangle
factors through the quotient term once its restriction to the left term vanishes. -/
lemma exists_factor_through_extension_quotient_of_precomp_zero
    {E₁ E E₂ Y : DMod} {f : E₁ ⟶ E} {g : E ⟶ E₂} {h : E₂ ⟶ E₁⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang DMod)
    {k : E ⟶ Y} (hk : f ≫ k = 0) :
    ∃ q : E₂ ⟶ Y, k = g ≫ q := by
  -- The represented contravariant Hom functor is exact on distinguished triangles.
  simpa using Triangle.yoneda_exact₂ (T := Triangle.mk f g h) hT k hk

/-- Helper for Lemma 15.80.1: evaluation at `1` identifies a morphism out of the free rank-one
module with the image of the generator. -/
lemma hom_from_ring_add_equiv_left_inv {N : ModuleCat R} (x : N) :
    (ModuleCat.homEquiv (ModuleCat.ofHom ((LinearMap.id : R →ₗ[R] R).smulRight x))) (1 : R) = x := by
  -- The inverse sends `x` to the linear map `r ↦ r • x`, which evaluates to `x` at `1`.
  change (((LinearMap.id : R →ₗ[R] R).smulRight x) (1 : R)) = x
  simp [LinearMap.smulRight_apply]

/-- Helper for Lemma 15.80.1: a morphism out of the free rank-one module is recovered from the
image of `1`. -/
lemma hom_from_ring_add_equiv_right_inv {N : ModuleCat R}
    (f : (ModuleCat.of R R) ⟶ N) :
    ModuleCat.ofHom (((LinearMap.id : R →ₗ[R] R).smulRight ((ModuleCat.homEquiv f) (1 : R)))) = f := by
  -- Extensionality reduces the claim to the `R`-linearity relation `f (x • 1) = x • f 1`.
  apply ModuleCat.hom_injective
  exact LinearMap.ext fun x ↦ by
    simp [LinearMap.smulRight_apply]
    simpa using ((ModuleCat.homEquiv f).map_smul x (1 : R)).symm

/-- Helper for Lemma 15.80.1: evaluation at `1` preserves addition on morphisms out of `R`. -/
lemma hom_from_ring_add_equiv_map_add {N : ModuleCat R}
    (f g : (ModuleCat.of R R) ⟶ N) :
    (ModuleCat.homEquiv (f + g)) (1 : R) =
      (ModuleCat.homEquiv f) (1 : R) + (ModuleCat.homEquiv g) (1 : R) :=
  rfl

/-- Helper for Lemma 15.80.1: morphisms out of the free rank-one module `R` are additively
equivalent to elements of the target module. -/
noncomputable def hom_from_ring_add_equiv (N : ModuleCat R) :
    ((ModuleCat.of R R) ⟶ N) ≃+ N :=
  { toFun := fun f ↦ (ModuleCat.homEquiv f) (1 : R)
    invFun := fun x ↦ ModuleCat.ofHom ((LinearMap.id : R →ₗ[R] R).smulRight x)
    left_inv := hom_from_ring_add_equiv_right_inv (R := R)
    right_inv := hom_from_ring_add_equiv_left_inv (R := R)
    map_add' := hom_from_ring_add_equiv_map_add (R := R) }

/-- Helper for Lemma 15.80.1: shifting `R[0]` by `k` identifies it with the single object
`R[-k]`. -/
noncomputable def shifted_ringSingle_iso_single (k : ℤ) :
    (ringSingle : DMod)⟦k⟧ ≅
      (DerivedCategory.singleFunctor (ModuleCat R) (-k)).obj (ModuleCat.of R R) :=
  ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso k (-k) 0 (by omega)).app
    (ModuleCat.of R R)

/-- Helper for Lemma 15.80.1: precomposing with the canonical shift identification transports maps
out of `R[0]⟦k⟧` to maps out of `R[-k]`. -/
noncomputable def shifted_ringSingle_hom_transport (X : DMod) (k : ℤ) :
    (((ringSingle : DMod)⟦k⟧) ⟶ X) ≃+
      (((DerivedCategory.singleFunctor (ModuleCat R) (-k)).obj (ModuleCat.of R R)) ⟶ X) :=
  { toFun := fun g ↦ (shifted_ringSingle_iso_single (R := R) k).inv ≫ g
    invFun := fun g ↦ (shifted_ringSingle_iso_single (R := R) k).hom ≫ g
    left_inv := by
      intro g
      -- Cancel the inverse pair of the shift isomorphism on the source.
      simpa [Category.assoc] using
        (Iso.hom_inv_id_assoc (shifted_ringSingle_iso_single (R := R) k) g)
    right_inv := by
      intro g
      -- Cancel the inverse pair of the shift isomorphism on the source.
      simpa [Category.assoc] using
        (Iso.inv_hom_id_assoc (shifted_ringSingle_iso_single (R := R) k) g)
    map_add' := by
      intro g h
      simp }

/-- Helper for Lemma 15.80.1: an object concentrated in degree `i` is canonically the single
object on its degree-`i` cohomology. -/
noncomputable def singleFunctorIsoOfIsGEOfIsLE_local
    (X : DMod) (i : ℤ) [X.IsGE i] [X.IsLE i] :
    X ≅ (DerivedCategory.singleFunctor (ModuleCat R) i).obj ((H^i).obj X) := by
  let hX := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X i
  let Y := Classical.choose hX
  let e : X ≅ (DerivedCategory.singleFunctor (ModuleCat R) i).obj Y :=
    Classical.choice (Classical.choose_spec hX)
  let eH : (H^i).obj X ≅ Y :=
    (H^i).mapIso e ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) i).app Y
  -- Replace the chosen concentrated model by the canonical one indexed by `H^i(X)`.
  exact e ≪≫ (DerivedCategory.singleFunctor (ModuleCat R) i).mapIso eH.symm

/-- Helper for Lemma 15.80.1: the lower truncation step preserves degree-`i` cohomology. -/
noncomputable def truncGE_step_homologyIso_local
    (X : DMod) (i : ℤ) :
    (H^i).obj
        ((DerivedCategory.TStructure.t.truncLT (i + 1)).obj
          ((DerivedCategory.TStructure.t.truncGE i).obj X)) ≅
      (H^i).obj X := by
  let eι :
      (H^i).obj
          ((DerivedCategory.TStructure.t.truncLT (i + 1)).obj
            ((DerivedCategory.TStructure.t.truncGE i).obj X)) ≅
        (H^i).obj ((DerivedCategory.TStructure.t.truncGE i).obj X) := by
    exact @asIso _ _ _ _
      ((H^i).map
        ((DerivedCategory.TStructure.t.truncLTι (i + 1)).app
          ((DerivedCategory.TStructure.t.truncGE i).obj X)))
      (isIso_homologyMap_truncLTι (A := ModuleCat R)
        ((DerivedCategory.TStructure.t.truncGE i).obj X) i (i + 1) rfl)
  let eπ : (H^i).obj X ≅ (H^i).obj ((DerivedCategory.TStructure.t.truncGE i).obj X) := by
    exact @asIso _ _ _ _
      ((H^i).map ((DerivedCategory.TStructure.t.truncGEπ i).app X))
      (isIso_homologyMap_truncGEπ (A := ModuleCat R) X i)
  -- Both truncation comparison maps are isomorphisms on `H^i`, so the middle cohomology agrees
  -- with that of `X`.
  exact eι ≪≫ eπ.symm

/-- Helper for Lemma 15.80.1: the degree-`i` lower truncation piece is the single object on
`H^i(X)`. -/
noncomputable def truncGE_step_termIso_local
    (X : DMod) (i : ℤ) :
    ((DerivedCategory.TStructure.t.truncLT (i + 1)).obj
      ((DerivedCategory.TStructure.t.truncGE i).obj X)) ≅
        (DerivedCategory.singleFunctor (ModuleCat R) i).obj ((H^i).obj X) := by
  haveI :
      ((DerivedCategory.TStructure.t.truncLT (i + 1)).obj
        ((DerivedCategory.TStructure.t.truncGE i).obj X)).IsLE i := by
    simpa using
      (inferInstance :
        ((DerivedCategory.TStructure.t.truncLT (i + 1)).obj
          ((DerivedCategory.TStructure.t.truncGE i).obj X)).IsLE ((i + 1) - 1))
  -- The truncation piece is supported in the single degree `i`, so the previous concentrated
  -- object comparison applies.
  exact
    singleFunctorIsoOfIsGEOfIsLE_local (R := R)
      ((DerivedCategory.TStructure.t.truncLT (i + 1)).obj
        ((DerivedCategory.TStructure.t.truncGE i).obj X)) i ≪≫
      (DerivedCategory.singleFunctor (ModuleCat R) i).mapIso
        (truncGE_step_homologyIso_local (R := R) X i)

/-- Helper for Lemma 15.80.1: the degree-`i` truncation sandwich is the single object on
`H^i(X)`. -/
noncomputable def truncGELT_termIso (X : DMod) (i : ℤ) :
    (DerivedCategory.TStructure.t.truncGE i).obj
        ((DerivedCategory.TStructure.t.truncLT (i + 1)).obj X) ≅
      (DerivedCategory.singleFunctor (ModuleCat R) i).obj ((H^i).obj X) :=
  -- Commute the two truncations, then identify the resulting one-step lower piece with
  -- `H^i(X)[-i]`.
  (DerivedCategory.TStructure.t.truncGELTIsoLTGE i (i + 1)).app X ≪≫
    truncGE_step_termIso_local (R := R) X i

/-- Helper for Lemma 15.80.1: a morphism between degree-`i` single objects is zero once its
degree-`i` cohomology map is zero. -/
lemma single_map_eq_zero_of_homologyMap_eq_zero
    {M N : ModuleCat R} {i : ℤ}
    (q : (DerivedCategory.singleFunctor (ModuleCat R) i).obj M ⟶
      (DerivedCategory.singleFunctor (ModuleCat R) i).obj N)
    (hq : (H^i).map q = 0) :
    q = 0 := by
  let hFF : (DerivedCategory.singleFunctor (ModuleCat R) i).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.singleFunctor (ModuleCat R) i)
  let u : M ⟶ N := hFF.preimage q
  have huq : (DerivedCategory.singleFunctor (ModuleCat R) i).map u = q := by
    simpa [u] using hFF.map_preimage q
  -- Naturality of the comparison `singleFunctor ⋙ H^i ≅ 𝟭` identifies the represented morphism
  -- with the degree-`i` cohomology map.
  have hu :
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) i).app M).hom ≫ u = 0 := by
    simpa [Functor.comp_map, huq, hq] using
      (NatTrans.naturality
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) i).hom u).symm
  have hu_zero : u = 0 := by
    exact
      (cancel_epi
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) i).app M).hom).1 hu
  -- Full faithfulness turns the zero module map back into the zero derived morphism.
  rw [← huq, hu_zero]
  simp

/-- Helper for Lemma 15.80.1: a ghost map vanishes after precomposition with any map from a shift
of the ring object `R[0]`. -/
lemma ghost_precompose_zero_of_shifted_ringSingle
    {A B : DMod} (f : A ⟶ B)
    (hghost : ∀ i : ℤ, (H^i).map f = 0)
    (k : ℤ) (g : (ringSingle : DMod)⟦k⟧ ⟶ A) :
    g ≫ f = 0 := by
  let g' :
      (DerivedCategory.singleFunctor (ModuleCat R) (-k)).obj (ModuleCat.of R R) ⟶ A :=
    shifted_ringSingle_hom_transport (R := R) A k g
  let i : ℤ := -k
  let h :
      (DerivedCategory.singleFunctor (ModuleCat R) i).obj (ModuleCat.of R R) ⟶ B :=
    g' ≫ f
  let hLT :
      (DerivedCategory.singleFunctor (ModuleCat R) i).obj (ModuleCat.of R R) ⟶
        (DerivedCategory.TStructure.t.truncLT (i + 1)).obj B :=
    DerivedCategory.TStructure.t.liftTruncLT h i (i + 1) rfl
  let hZero :
      (DerivedCategory.singleFunctor (ModuleCat R) i).obj (ModuleCat.of R R) ⟶
        (DerivedCategory.TStructure.t.truncGE i).obj
          ((DerivedCategory.TStructure.t.truncLT (i + 1)).obj B) :=
    hLT ≫ (DerivedCategory.TStructure.t.truncGEπ i).app
      ((DerivedCategory.TStructure.t.truncLT (i + 1)).obj B)
  let hSingle :
      (DerivedCategory.singleFunctor (ModuleCat R) i).obj (ModuleCat.of R R) ⟶
        (DerivedCategory.singleFunctor (ModuleCat R) i).obj ((H^i).obj B) :=
    hZero ≫ (truncGELT_termIso (R := R) B i).hom
  have hh_zero : (H^i).map h = 0 := by
    -- The ghost hypothesis annihilates the degree-`i` cohomology map of the composite.
    simpa [h, Functor.map_comp, hghost i]
  have hLT_zero : (H^i).map hLT = 0 := by
    -- The upper truncation inclusion is an isomorphism on `H^i`, so the lifted map is already
    -- cohomologically zero in degree `i`.
    letI :
        IsIso ((H^i).map ((DerivedCategory.TStructure.t.truncLTι (i + 1)).app B)) :=
      isIso_homologyMap_truncLTι (A := ModuleCat R) B i (i + 1) rfl
    have hfac :
        (H^i).map hLT ≫ (H^i).map ((DerivedCategory.TStructure.t.truncLTι (i + 1)).app B) =
          (H^i).map h := by
      simpa [hLT, Functor.map_comp] using
        congrArg (fun t ↦ (H^i).map t)
          (DerivedCategory.TStructure.t.liftTruncLT_ι h i (i + 1) rfl)
    apply (cancel_mono ((H^i).map ((DerivedCategory.TStructure.t.truncLTι (i + 1)).app B))).1
    simpa [hh_zero] using hfac
  have hZero_zero : (H^i).map hZero = 0 := by
    -- Passing to the degree-`i` truncation piece preserves the same vanishing.
    simp [hZero, Functor.map_comp, hLT_zero]
  have hSingle_zero : (H^i).map hSingle = 0 := by
    -- After identifying the truncation piece with a single object, nothing changes on `H^i`.
    simp [hSingle, Functor.map_comp, hZero_zero]
  have hSingle_eq_zero : hSingle = 0 :=
    single_map_eq_zero_of_homologyMap_eq_zero (R := R) hSingle hSingle_zero
  have hZero_eq_zero : hZero = 0 := by
    -- The comparison to the single object is an isomorphism, so its source morphism is zero.
    apply (cancel_mono (truncGELT_termIso (R := R) B i).hom).1
    simpa [hSingle, hSingle_eq_zero]
  let T : Triangle DMod :=
    (DerivedCategory.TStructure.t.triangleLTGE i).obj
      ((DerivedCategory.TStructure.t.truncLT (i + 1)).obj B)
  have hT : T ∈ distTriang DMod := by
    simpa [T] using
      DerivedCategory.TStructure.t.triangleLTGE_distinguished i
        ((DerivedCategory.TStructure.t.truncLT (i + 1)).obj B)
  obtain ⟨u, hu⟩ := Triangle.coyoneda_exact₂ (T := T) hT hLT (by
    -- Exactness now forces the lifted map to factor through the strictly lower truncation.
    simpa [T, hZero] using hZero_eq_zero)
  have hu_zero : u = 0 := by
    let hLow :
        ((DerivedCategory.TStructure.t.truncLT i).obj
          ((DerivedCategory.TStructure.t.truncLT (i + 1)).obj B)).IsLE (i - 1) :=
      inferInstance
    rcases hLow with ⟨L, eL, hL⟩
    have hu' : u ≫ eL.hom = 0 := by
      -- Projectivity of `R` kills maps from `R[-i]` into complexes supported strictly below `i`.
      simpa using
        (DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective
          (P := ModuleCat.of R R) (L := L) (i := i) (φ := u ≫ eL.hom) (n := i - 1)
          (hn := by omega))
    apply (cancel_mono eL.hom).1
    simpa using hu'
  have hLT_eq_zero : hLT = 0 := by
    -- The factorization through the lower truncation collapses because that factor is zero.
    rw [hu_zero] at hu
    calc
      hLT = 0 ≫ T.mor₁ := hu
      _ = 0 := by simp
  have hh_eq_zero : h = 0 := by
    -- Compose back with `τ_{< i+1} B ⟶ B` to return to the original composite.
    calc
      h = hLT ≫ (DerivedCategory.TStructure.t.truncLTι (i + 1)).app B := by
        simpa [hLT] using
          (DerivedCategory.TStructure.t.liftTruncLT_ι h i (i + 1) rfl).symm
      _ = 0 := by
        rw [hLT_eq_zero, zero_comp]
  have hg_transport :
      g = (shifted_ringSingle_iso_single (R := R) k).hom ≫ g' := by
    -- Expanding the transport equivalence recovers the original shifted-source morphism.
    simpa [g', shifted_ringSingle_hom_transport]
  -- Undo the source transport to conclude for the original map `g`.
  rw [hg_transport]
  simpa [h, i, Category.assoc] using
    congrArg (fun t ↦ (shifted_ringSingle_iso_single (R := R) k).hom ≫ t) hh_eq_zero

/-- Helper for Lemma 15.80.1: the stage-one generated objects are annihilated by a single ghost
after precomposition. -/
lemma ghost_precompose_zero_of_mem_stage_one
    {A B E : DMod} (f : A ⟶ B)
    (hghost : ∀ i : ℤ, (H^i).map f = 0)
    (hE : (⟨ringSingle⟩_(1 : ℕ+)) E) (g : E ⟶ A) :
    g ≫ f = 0 := by
  let P : ObjectProperty DMod := fun X ↦ ∀ h : X ⟶ A, h ≫ f = 0
  letI : P.IsStableUnderRetracts := ⟨by
    intro X Y r hY h
    -- A retract lifts a test morphism to the larger object where the vanishing is known.
    have hcomp : r.r ≫ h ≫ f = 0 := by
      simpa [Category.assoc] using hY (r.r ≫ h)
    simpa [Category.assoc] using congrArg (fun t ↦ r.i ≫ t) hcomp⟩
  letI : P.ContainsZero := {
    exists_zero := by
      refine ⟨(0 : DerivedCategory (ModuleCat R)),
        Limits.isZero_zero (DerivedCategory (ModuleCat R)), ?_⟩
      intro h
      have hh :
          h = (0 : (0 : DerivedCategory (ModuleCat R)) ⟶ A) := Subsingleton.elim _ _
      simpa [hh]
  }
  letI : P.IsClosedUnderBinaryCoproducts := by
    refine ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
    rintro Z ⟨F, hF⟩
    intro h
    apply colimit.hom_ext
    intro j
    -- Vanishing on a binary coproduct is checked on the two coproduct summands.
    simpa [Category.assoc] using hF j (colimit.ι F j ≫ h)
  letI : P.IsClosedUnderFiniteCoproducts :=
    ObjectProperty.IsClosedUnderFiniteCoproducts.mk'
  -- The stage-one description reduces to the additive and retract closure of shifts of `R[0]`.
  have hShift : ((ObjectProperty.singleton (ringSingle : DMod)).shiftClosure ℤ) ≤ P := by
    intro X hX
    rw [ObjectProperty.prop_shiftClosure_iff] at hX
    rcases hX with ⟨Y, k, e, hY⟩
    rw [ObjectProperty.singleton_iff] at hY
    subst hY
    intro g
    have hg_zero : e.inv ≫ g ≫ f = 0 := by
      simpa [Category.assoc] using
        ghost_precompose_zero_of_shifted_ringSingle (f := f) hghost k (e.inv ≫ g)
    calc
      g ≫ f = e.hom ≫ (e.inv ≫ g) ≫ f := by simp [Category.assoc]
      _ = 0 := by simpa [Category.assoc] using congrArg (fun t ↦ e.hom ≫ t) hg_zero
  have hP : ((ObjectProperty.singleton (ringSingle : DMod)).shiftClosure ℤ).additiveClosure ≤ P := by
    refine colimitsClosure_le ?_
    exact hShift
  have hP' :
      ((ObjectProperty.singleton (ringSingle : DMod)).shiftClosure ℤ).additiveClosure.retractClosure ≤ P := by
    rw [retractClosure_le_iff]
    exact hP
  rw [objectGeneratedStage_one_eq] at hE
  exact hP' _ hE g

/-- Helper for Lemma 15.80.1: an `n`-fold ghost composite is annihilated after precomposition by
any map from an object of the `n`-th stage generated by `R[0]`. -/
lemma ghost_chain_precompose_zero_of_mem_objectGeneratedStage
    {n : ℕ+} {X : ComposableArrows DMod n} {E : DMod}
    (hX : (⟨ringSingle⟩_n) E)
    (hghost : ∀ j : ℕ, (hj : j < n) → ∀ i : ℤ, (H^i).map (X.arrow j hj).hom = 0)
    (u : E ⟶ X.left) :
    u ≫ X.hom = 0 := by
  -- Route correction: the interval/truncation sketch is too strong for stage one, so the proof
  -- should instead proceed by induction on `n` through `objectGeneratedStage_succ`.
  refine (@PNat.recOn n
    (fun n : ℕ+ ↦
      ∀ {X : ComposableArrows DMod n} {E : DMod},
        (⟨ringSingle⟩_n) E →
          (∀ j : ℕ, (hj : j < n) → ∀ i : ℤ, (H^i).map (X.arrow j hj).hom = 0) →
            ∀ u : E ⟶ X.left, u ≫ X.hom = 0)
    ?_ ?_ (X := X) (E := E) hX hghost u)
  · intro X E hE hghost u
    -- In a chain of length one, the unique arrow is already the whole composite.
    have hghost₀ : ∀ i : ℤ, (H^i).map (X.arrow 0 (by decide)).hom = 0 := by
      intro i
      simpa using hghost 0 (by decide) i
    simpa [ComposableArrows.arrow, ComposableArrows.hom] using
      ghost_precompose_zero_of_mem_stage_one
        (f := (X.arrow 0 (by decide)).hom) hghost₀ hE u
  · intro m ih X E hE hghost u
    let P : ObjectProperty DMod := fun Y ↦ ∀ v : Y ⟶ X.left, v ≫ X.hom = 0
    letI : P.IsStableUnderRetracts := ⟨by
      intro Y Z r hY v
      -- A retract lifts a test morphism to the ambient extension where the inductive vanishing
      -- statement is already known.
      have hcomp : r.r ≫ v ≫ X.hom = 0 := by
        simpa [Category.assoc] using hY (r.r ≫ v)
      calc
        v ≫ X.hom = r.i ≫ (r.r ≫ v ≫ X.hom) := by simp
        _ = r.i ≫ 0 := by rw [hcomp]
        _ = 0 := by rw [comp_zero]⟩
    have hstage : (⟨ringSingle⟩_(m + 1)) ≤ P := by
      rw [objectGeneratedStage_succ, retractClosure_le_iff]
      intro Y hY v
      rw [extensionProduct_iff] at hY
      rcases hY with ⟨Y₁, Y₂, a, b, c, hT, hY₁, hY₂⟩
      have hzero_lt : (0 : ℕ) < (m + 1 : ℕ+) := by
        exact PNat.pos (m + 1)
      have hghost₀ : ∀ i : ℤ, (H^i).map (X.arrow 0 hzero_lt).hom = 0 := by
        intro i
        simpa using hghost 0 hzero_lt i
      -- The head ghost kills the restriction of `v` to the stage-one piece.
      have ha_zero : a ≫ v ≫ (X.arrow 0 hzero_lt).hom = 0 := by
        simpa [Category.assoc] using
          ghost_precompose_zero_of_mem_stage_one
            (f := (X.arrow 0 hzero_lt).hom) hghost₀ hY₁ (a ≫ v)
      -- Exactness of the defining triangle produces a factor through the quotient stage.
      obtain ⟨q, hq⟩ :=
        exists_factor_through_extension_quotient_of_precomp_zero
          hT (k := v ≫ (X.arrow 0 hzero_lt).hom) ha_zero
      have hghost_tail :
          ∀ j : ℕ, (hj : j < m) → ∀ i : ℤ, (H^i).map (X.δ₀.arrow j hj).hom = 0 := by
        intro j hj i
        simpa [ComposableArrows.arrow, ComposableArrows.δ₀] using
          hghost (j + 1) (Nat.succ_lt_succ hj) i
      have htail : q ≫ X.δ₀.hom = 0 :=
        ih (X := X.δ₀) (E := Y₂) hY₂ hghost_tail q
      have hhom : X.hom = (X.arrow 0 hzero_lt).hom ≫ X.δ₀.hom := by
        simpa [ComposableArrows.arrow, ComposableArrows.δ₀, ComposableArrows.hom] using
          (X.map'_comp 0 1 (m + 1 : ℕ))
      -- Rewrite the total composite as head arrow followed by the tail composite.
      calc
        v ≫ X.hom = v ≫ (X.arrow 0 hzero_lt).hom ≫ X.δ₀.hom := by
          rw [hhom]
          rfl
        _ = b ≫ q ≫ X.δ₀.hom := by
          calc
            v ≫ (X.arrow 0 hzero_lt).hom ≫ X.δ₀.hom =
                (v ≫ (X.arrow 0 hzero_lt).hom) ≫ X.δ₀.hom := by
                  simp [Category.assoc]
            _ = (b ≫ q) ≫ X.δ₀.hom := by rw [hq]
            _ = b ≫ q ≫ X.δ₀.hom := by simp [Category.assoc]
        _ = 0 := by
          calc
            b ≫ q ≫ X.δ₀.hom = b ≫ (q ≫ X.δ₀.hom) := by simp
            _ = b ≫ 0 := by rw [htail]
            _ = 0 := by rw [comp_zero]
    exact hstage _ hE u

/-- Lemma 15.80.1: if the leftmost object of a chain of composable morphisms in `D(R)` lies in
`⟨R[0]⟩_n` and every arrow is ghost, then the composite of the chain is zero. -/
@[stacks 0FXH]
theorem ghost_composite_zero_of_mem_objectGeneratedStage
    {n : ℕ+} {X : ComposableArrows DMod n}
    (hX : (⟨ringSingle⟩_n) X.left)
    (hghost : ∀ j : ℕ, (hj : j < n) → ∀ i : ℤ, (H^i).map (X.arrow j hj).hom = 0) :
    X.hom = 0 := by
  -- The strengthened precomposition statement finishes the textbook theorem by taking `u = 𝟙`.
  simpa using
    ghost_chain_precompose_zero_of_mem_objectGeneratedStage
      (X := X) (E := X.left) hX hghost (𝟙 X.left)

end

end CategoryTheory
