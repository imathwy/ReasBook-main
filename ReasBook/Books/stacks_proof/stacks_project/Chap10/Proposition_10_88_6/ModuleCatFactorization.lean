import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.TFAE
import stacks_proof.stacks_project.Chap10.Definition_10_88_2
import stacks_proof.stacks_project.Chap10.Lemma_10_11_1
import stacks_proof.stacks_project.Chap10.Lemma_10_11_4
import stacks_proof.stacks_project.Chap10.Lemma_10_79_4
import stacks_proof.stacks_project.Chap10.Lemma_10_82_14
import stacks_proof.stacks_project.Chap10.Lemma_10_88_3
import stacks_proof.stacks_project.Chap10.Lemma_10_88_5
import stacks_proof.stacks_project.Chap10.Proposition_10_88_6.CommonUniverseOwners
import stacks_proof.stacks_project.Chap10.Proposition_10_88_6.TensorDomination

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped TensorProduct MonoidalCategory

universe u v w

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {M : Type (max v w)} [AddCommGroup M] [Module R M]

/-- Helper for Proposition 10.88.6: a domination hypothesis can be specialized to any bundled
test object in `ModuleCat.{max v w} R` without reopening universe metavariables. -/
lemma LinearMap.kernel_le_of_dominates_bundled_testObject_frozen
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (hdom : g.Dominates f)
    (N : ModuleCat.{max v w} R) :
    LinearMap.ker (f.rTensor N) ≤ LinearMap.ker (g.rTensor N) := by
  let eA : A ⊗[R] N ≃ₗ[R] A ⊗[R] ULift.{u} N :=
    TensorProduct.congr (LinearEquiv.refl R A) ULift.moduleEquiv.symm
  let eB : B ⊗[R] N ≃ₗ[R] B ⊗[R] ULift.{u} N :=
    TensorProduct.congr (LinearEquiv.refl R B) ULift.moduleEquiv.symm
  let eC : C ⊗[R] N ≃ₗ[R] C ⊗[R] ULift.{u} N :=
    TensorProduct.congr (LinearEquiv.refl R C) ULift.moduleEquiv.symm
  have hf_apply (x : A ⊗[R] N) :
      (f.rTensor (ULift.{u} N)) (eA x) = eB ((f.rTensor N) x) := by
    -- Proof comment: changing the tensor factor from `N` to `ULift N` commutes with `f ⊗ 1`.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [eA, eB]
    · intro a n
      rfl
    · intro x₁ x₂ hx₁ hx₂
      simp [hx₁, hx₂]
  have hg_apply (x : A ⊗[R] N) :
      (g.rTensor (ULift.{u} N)) (eA x) = eC ((g.rTensor N) x) := by
    -- Proof comment: the same transport square holds for `g ⊗ 1`.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [eA, eC]
    · intro a n
      rfl
    · intro x₁ x₂ hx₁ hx₂
      simp [hx₁, hx₂]
  intro x hx
  have hx_zero : (f.rTensor N) x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  have hx_lift :
      (f.rTensor (ULift.{u} N)) (eA x) = 0 := by
    calc
      (f.rTensor (ULift.{u} N)) (eA x)
          = eB ((f.rTensor N) x) := hf_apply x
      _ = 0 := by simp [hx_zero]
  have hx_lift_mem :
      eA x ∈ LinearMap.ker (f.rTensor (ULift.{u} N)) := by
    simpa [LinearMap.mem_ker] using hx_lift
  have hy_lift_mem :
      eA x ∈ LinearMap.ker (g.rTensor (ULift.{u} N)) := hdom (ULift.{u} N) hx_lift_mem
  have hy_lift : (g.rTensor (ULift.{u} N)) (eA x) = 0 := by
    simpa [LinearMap.mem_ker] using hy_lift_mem
  have hy_zero : (g.rTensor N) x = 0 := by
    apply eC.injective
    calc
      eC ((g.rTensor N) x)
          = (g.rTensor (ULift.{u} N)) (eA x) := by
              symm
              exact hg_apply x
      _ = 0 := hy_lift
      _ = eC 0 := by simp [eC]
  simpa [LinearMap.mem_ker] using hy_zero
/-- Helper for Proposition 10.88.6: domination of stage maps is preserved after precomposition by
a bundled `ModuleCat` morphism. -/
lemma moduleCat_hom_dominates_precompose
    {P A B C : ModuleCat.{max v w} R}
    (u : P ⟶ A) (f : A ⟶ B) (g : A ⟶ C)
    (hdom : g.hom.Dominates f.hom) :
    (u ≫ g).hom.Dominates (u ≫ f).hom := by
  -- This is the bundled form of the linear-algebra fact that domination is stable under
  -- precomposition.
  intro Q
  intro _ _
  intro x hx
  have hx' : (u.hom.rTensor Q) x ∈ LinearMap.ker (f.hom.rTensor Q) := by
    simpa [LinearMap.mem_ker, LinearMap.rTensor_comp] using hx
  have hx'' : (u.hom.rTensor Q) x ∈ LinearMap.ker (g.hom.rTensor Q) := hdom Q hx'
  simpa [LinearMap.mem_ker, LinearMap.rTensor_comp] using hx''

/-- Helper for Proposition 10.88.6: if a stage map dominates a colimit map with codomain frozen to
`ModuleCat.of R M`, then the same domination persists after precomposing with a bundled source
map. -/
lemma moduleCat_hom_dominates_precompose_codomain_frozen
    {P A B : ModuleCat.{max v w} R}
    (u : P ⟶ A) (v : A ⟶ B) (w : A ⟶ ModuleCat.of R M)
    (hdom : v.hom.Dominates w.hom) :
    (u ≫ v).hom.Dominates (u ≫ w).hom := by
  let u' : (P : Type (max v w)) →ₗ[R] (A : Type (max v w)) := u.hom
  let v' : (A : Type (max v w)) →ₗ[R] (B : Type (max v w)) := v.hom
  let w' : (A : Type (max v w)) →ₗ[R] M := w.hom
  intro Q
  intro _ _
  intro x hx
  have hx' : (u'.rTensor Q) x ∈ LinearMap.ker (w'.rTensor Q) := by
    -- Proof comment: rewrite the tensor of the precomposed colimit map as the composite of the
    -- tensorized source map with the frozen codomain map.
    simpa [u', w', LinearMap.mem_ker, LinearMap.rTensor_comp] using hx
  have hy' : (u'.rTensor Q) x ∈ LinearMap.ker (v'.rTensor Q) := hdom Q hx'
  -- Proof comment: translate the resulting kernel membership back to the tensor of the bundled
  -- composite into stage `B`.
  simpa [u', v', LinearMap.mem_ker, LinearMap.rTensor_comp] using hy'

/-- Helper for Proposition 10.88.6: the underlying linear map of a composite `ModuleCat`
morphism is the composite of the underlying linear maps. -/
lemma moduleCat_comp_hom_typed
    {P A B : ModuleCat.{max v w} R}
    (u : P ⟶ A) (v : A ⟶ B) :
    (((u ≫ v).hom) : (P : Type (max v w)) →ₗ[R] (B : Type (max v w))) = v.hom.comp u.hom := by
  -- Proof comment: both sides are definitionally the same linear map `x ↦ v (u x)`.
  ext x
  rfl

/-- Helper for Proposition 10.88.6: tensoring a composite bundled morphism matches the composite
of the tensorized underlying linear maps. -/
lemma moduleCat_comp_hom_rTensor_eq_typed
    {P A B : ModuleCat.{max v w} R}
    (u : P ⟶ A) (v : A ⟶ B)
    (N : ModuleCat.{max v w} R) :
    ((((u ≫ v).hom).rTensor N) : P ⊗[R] N →ₗ[R] B ⊗[R] N) =
      (v.hom.rTensor N).comp (u.hom.rTensor N) := by
  -- Proof comment: both sides are linear in the tensor variable, so it suffices to compare them
  -- on pure tensors where the formula is definitionally `v (u p) ⊗ n`.
  refine LinearMap.ext fun x : P ⊗[R] N => ?_
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro p n
    rfl
  · intro x₁ x₂ hx₁ hx₂
    rw [LinearMap.map_add, LinearMap.map_add, hx₁, hx₂]

/-- Helper for Proposition 10.88.6: equality of bundled `ModuleCat` morphisms is detected on the
underlying linear maps. -/
lemma moduleCat_hom_eq_iff_hom_eq
    {A B : ModuleCat.{max v w} R} {f g : A ⟶ B} :
    f = g ↔ f.hom = g.hom := by
  constructor
  · intro h
    simpa [h]
  · intro h
    exact ModuleCat.hom_ext h

/-- Helper for Proposition 10.88.6: bundling a linear map into `ModuleCat` is injective on the
underlying map. -/
lemma moduleCat_ofHom_eq_iff
    {A B : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    {f g : A →ₗ[R] B} :
    ModuleCat.ofHom f = ModuleCat.ofHom g ↔ f = g := by
  constructor
  · intro h
    exact congrArg ModuleCat.Hom.hom h
  · intro h
    simpa [h]

/-- Helper for Proposition 10.88.6: a bundled factorization is equivalent to the corresponding
factorization of underlying linear maps. -/
lemma moduleCat_hom_factorization_iff_hom_factorization
    {A B C : ModuleCat.{max v w} R} (f : A ⟶ B) (g : A ⟶ C) :
    (∃ h : B ⟶ C, g = f ≫ h) ↔ ∃ h : B →ₗ[R] C, g.hom = h.comp f.hom := by
  constructor
  · rintro ⟨h, rfl⟩
    -- Proof comment: forgetting a bundled factorization just forgets the codomain map.
    refine ⟨h.hom, ?_⟩
    ext x
    rfl
  · rintro ⟨h, hh⟩
    -- Proof comment: bundling the linear factor map converts the unbundled equality back into a
    -- categorical factorization.
    refine ⟨ModuleCat.ofHom h, ?_⟩
    apply ModuleCat.hom_ext
    simpa [ModuleCat.ofHom_comp] using hh

/-- Helper for Proposition 10.88.6: once the carrier types are frozen to the ambient stage
universe, lifting source and target by `ULift` preserves factorization. -/
lemma LinearMap.factorization_iff_exists_ulift_factorization_frozen
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C} :
    (∃ h : B →ₗ[R] C, g = h.comp f) ↔
      ∃ h : ULift.{u} B →ₗ[R] ULift.{u} C,
        LinearMap.ulift_map (R := R) g =
          h.comp (LinearMap.ulift_map (R := R) f) := by
  -- Proof comment: this is the existing `ULift`-carrier factorization criterion, specialized to
  -- the exact universe level used by the directed-system stages so later calls do not reopen
  -- universe metavariables.
  exact
    LinearMap.factorization_iff_exists_ulift_factorization
      (R := R) (f := f) (g := g)
/-- Helper for Proposition 10.88.6: a displayed linear factorization can be evaluated pointwise. -/
lemma linear_factorization_apply
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C} {h : B →ₗ[R] C}
    (hh : g = h.comp f) (x : A) :
    g x = h (f x) := by
  simpa [hh]

/-- Helper for Proposition 10.88.6: forgetting a chosen stage factorization yields the
corresponding equality of underlying linear maps. -/
lemma stage_factorization_hom_eq
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {P : ModuleCat.{max v w} R}
    {i : I}
    (g₀ : P ⟶ F.obj i)
    (f : P →ₗ[R] M)
    (hg₀ : g₀ ≫ (colimit.ι F i ≫ c.hom) = ModuleCat.ofHom f) :
    (g₀ ≫ (colimit.ι F i ≫ c.hom)).hom = f := by
  -- Proof comment: forgetting the bundled factorization is exactly the desired equality of
  -- underlying linear maps.
  simpa using congrArg ModuleCat.Hom.hom hg₀

/-- Helper for Proposition 10.88.6: evaluating the tensorized chosen stage factorization at a
tensor element agrees with tensoring the original map `f`. -/
lemma stage_factorization_rTensor_apply
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {P : ModuleCat.{max v w} R}
    {i : I}
    (g₀ : P ⟶ F.obj i)
    (f : P →ₗ[R] M)
    (hg₀ : g₀ ≫ (colimit.ι F i ≫ c.hom) = ModuleCat.ofHom f)
    {Q : Type (max u v w)} [AddCommMonoid Q] [Module R Q]
    (x : (P : Type (max v w)) ⊗[R] Q) :
    ((((g₀ ≫ (colimit.ι F i ≫ c.hom)).hom).rTensor Q) x) = (f.rTensor Q) x := by
  -- Proof comment: evaluate the tensorized stage-factorization identity on the chosen tensor
  -- element `x`.
  simpa using
    congrArg
      (fun t : (P : Type (max v w)) →ₗ[R] M ↦ (t.rTensor Q) x)
      (stage_factorization_hom_eq (R := R) (F := F) (c := c) (g₀ := g₀) (f := f) hg₀)

/-- Helper for Proposition 10.88.6: once a stage map represents `f ≫ c.inv` in the Hom-colimit,
postcomposing with the colimit isomorphism recovers the original map `f`. -/
lemma stage_factorization_of_colimit_iso_rep
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {P : ModuleCat.{max v w} R}
    {i : I}
    (g : P ⟶ F.obj i)
    (f : P ⟶ ModuleCat.of R M)
    (hg : g ≫ colimit.ι F i = f ≫ c.inv) :
    g ≫ (colimit.ι F i ≫ c.hom) = f := by
  -- Proof comment: the represented map first lands in `colimit F`; composing with `c.hom`
  -- cancels the inserted `c.inv` and returns to the original codomain.
  calc
    g ≫ (colimit.ι F i ≫ c.hom) = (g ≫ colimit.ι F i) ≫ c.hom := by
      simp [Category.assoc]
    _ = (f ≫ c.inv) ≫ c.hom := by
      simpa using congrArg (fun t ↦ t ≫ c.hom) hg
    _ = f := by
      simp [Category.assoc]

/-- Helper for Proposition 10.88.6: a map from a finitely presented module into the colimit
presentation factors through one stage. -/
lemma finite_presentation_factor_through_filtered_colimit_stage
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    (P : ModuleCat.{max v w} R)
    [Module.FinitePresentation R P]
    (f : P ⟶ ModuleCat.of R M) :
    ∃ (i : I) (g : P ⟶ F.obj i), g ≫ (colimit.ι F i ≫ c.hom) = f := by
  -- Route correction: the direct local `coyoneda` proof still runs into the same universe
  -- mismatch as the support owner, so this wrapper continues to use the imported lifted-index
  -- factorization owner for now.
  exact ulifted_factor_through_given_filtered_cocone_stage_of_finitePresentation
    (R := R) (F := F) (c := c) (P := P) f

/-- Helper for Proposition 10.88.6: a map from a finitely presented source module into the chosen
colimit object factors through one stage, with the source map given in unbundled linear-map form.
-/
lemma stage_factor_through_colimit_for_fp_source_explicit_universe
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    (P : ModuleCat.{max v w} R)
    [Module.FinitePresentation R P]
    (f : P →ₗ[R] M) :
    ∃ (i : I) (g : P ⟶ F.obj i), g ≫ (colimit.ι F i ≫ c.hom) = ModuleCat.ofHom f := by
  -- This is the clause-shaped wrapper around the bundled stage-factorization owner above.
  exact finite_presentation_factor_through_filtered_colimit_stage
    (R := R) (F := F) (c := c) (P := P) (ModuleCat.ofHom f)

/-- Helper for Proposition 10.88.6: two maps from a finitely presented stage into the same stage
which agree in the colimit agree after passing to a later transition map. -/
lemma eventually_equal_stage_maps_of_equal_colimit_composites
    (F : I ⥤ ModuleCat.{max v w} R)
    (hfp : ∀ i, Module.FinitePresentation R (F.obj i))
    {i j : I}
    (u v : F.obj i ⟶ F.obj j)
    (h : u ≫ colimit.ι F j = v ≫ colimit.ι F j) :
    ∃ (k : I) (hjk : j ≤ k), u ≫ F.map (homOfLE hjk) = v ≫ F.map (homOfLE hjk) := by
  letI : Module.Finite R (F.obj i) := inferInstance
  letI : IsDirectedOrder (ULift.{max v w} I) :=
    ⟨fun a b => by
      obtain ⟨k, hak, hbk⟩ := exists_ge_ge a.down b.down
      exact ⟨ULift.up k, hak, hbk⟩⟩
  have hcolim :
      colimit F =
        ModuleCat.of R ((colimit F : ModuleCat.{max v w} R) : Type (max v w)) := rfl
  let liftedCocone :
      Cocone (lifted_index_diagram (R := R) F) :=
    lifted_index_cocone (R := R)
      (M := ((colimit F : ModuleCat.{max v w} R) : Type (max v w)))
      F (eqToIso hcolim)
  let liftedIsColimit :
      IsColimit liftedCocone :=
    common_universe_lifted_index_isColimit (R := R)
      (M := ((colimit F : ModuleCat.{max v w} R) : Type (max v w)))
      F (eqToIso hcolim)
  let e : liftedCocone.pt ≅ colimit (lifted_index_diagram (R := R) F) :=
    liftedIsColimit.coconePointUniqueUpToIso
      (colimit.isColimit (lifted_index_diagram (R := R) F))
  have hleg :
      liftedCocone.ι.app (ULift.up j) ≫ e.hom =
        colimit.ι (lifted_index_diagram (R := R) F) (ULift.up j) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      liftedIsColimit (colimit.isColimit (lifted_index_diagram (R := R) F)) (ULift.up j)
  have h_post :
      u ≫ liftedCocone.ι.app (ULift.up j) ≫ e.hom =
        v ≫ liftedCocone.ι.app (ULift.up j) ≫ e.hom := by
    have h' : u ≫ liftedCocone.ι.app (ULift.up j) = v ≫ liftedCocone.ι.app (ULift.up j) := by
      simpa [liftedCocone, lifted_index_cocone] using h
    -- Proof comment: postcompose the original colimit equality with the comparison isomorphism to
    -- obtain equality against the canonical colimit cocone of the lifted diagram.
    simpa [Category.assoc] using congrArg (fun t ↦ t ≫ e.hom) h'
  have h_lifted :
      u ≫ colimit.ι (lifted_index_diagram (R := R) F) (ULift.up j) =
        v ≫ colimit.ι (lifted_index_diagram (R := R) F) (ULift.up j) := by
    -- Proof comment: identify the explicit lifted cocone with the canonical colimit cocone via the
    -- unique comparison isomorphism.
    calc
      u ≫ colimit.ι (lifted_index_diagram (R := R) F) (ULift.up j)
          = u ≫ liftedCocone.ι.app (ULift.up j) ≫ e.hom := by
              simpa [Category.assoc] using congrArg (fun t ↦ u ≫ t) hleg.symm
      _ = v ≫ liftedCocone.ι.app (ULift.up j) ≫ e.hom := h_post
      _ = v ≫ colimit.ι (lifted_index_diagram (R := R) F) (ULift.up j) := by
              simpa [Category.assoc] using congrArg (fun t ↦ v ≫ t) hleg
  -- Proof comment: apply the finite-module eventual-equality owner to the lifted index diagram,
  -- then descend the returned later stage back to `I`.
  obtain ⟨k, hk, hkv⟩ :=
    eventually_equal_of_hom_to_colimit_of_finite_module
      (R := R) (N := ModuleCat.of R (F.obj i)) (lifted_index_diagram (R := R) F) u v h_lifted
  refine ⟨k.down, hk.down.down, ?_⟩
  simpa [lifted_index_diagram] using hkv

/-- Helper for Proposition 10.88.6: the canonical map from stage `i` to the colimit factors
through every later transition map `M_i → M_k`. -/
lemma colimit_map_factors_through_transition
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i k : I} (hik : i ≤ k) :
    ∃ h : F.obj k ⟶ ModuleCat.of R M,
      F.map (homOfLE hik) ≫ h = colimit.ι F i ≫ c.hom := by
  refine ⟨colimit.ι F k ≫ c.hom, ?_⟩
  -- Proof comment: the cocone relation identifies the map from stage `i` to the colimit with the
  -- composite through every later stage `k`.
  simpa [Category.assoc] using congrArg (fun t ↦ t ≫ c.hom) (colimit.w F (homOfLE hik))

/-- Helper for Proposition 10.88.6: the morphism-level factorization through a later stage can be
read as an explicit linear-map factorization of the colimit map. -/
lemma colimit_map_factors_through_transition_hom
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i k : I} (hik : i ≤ k) :
    ∃ h : F.obj k →ₗ[R] M,
      (colimit.ι F i ≫ c.hom).hom = h.comp (F.map (homOfLE hik)).hom := by
  rcases colimit_map_factors_through_transition (R := R) (F := F) (c := c) hik with ⟨h, hh⟩
  refine ⟨h.hom, ?_⟩
  ext x
  -- Proof comment: forgetting the bundled morphisms turns the cocone identity into the desired
  -- factorization equality of linear maps.
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hh).symm x

/-- Helper for Proposition 10.88.6: the map from stage `i` to the colimit dominates every later
transition map out of stage `i`. -/
lemma colimit_map_dominates_transition
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i k : I} (hik : i ≤ k) :
    ((colimit.ι F i ≫ c.hom).hom).Dominates ((F.map (homOfLE hik)).hom) := by
  -- Proof comment: the colimit map factors through every later transition map, so its tensor
  -- kernel contains the tensor kernel of that transition map.
  intro N
  intro _ _
  intro x hx
  rcases colimit_map_factors_through_transition_hom (R := R) (F := F) (c := c) hik with ⟨h, hh⟩
  have hh_tensor :
      (((colimit.ι F i ≫ c.hom).hom).rTensor N) =
        (h.rTensor N).comp (((F.map (homOfLE hik)).hom).rTensor N) := by
    simpa [LinearMap.rTensor_comp] using
      congrArg (fun t : F.obj i →ₗ[R] M ↦ t.rTensor N) hh
  have hx_zero : (((F.map (homOfLE hik)).hom).rTensor N) x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  have hcolim_zero : (((colimit.ι F i ≫ c.hom).hom).rTensor N) x = 0 := by
    calc
      (((colimit.ι F i ≫ c.hom).hom).rTensor N) x
          = ((h.rTensor N).comp (((F.map (homOfLE hik)).hom).rTensor N)) x := by
              rw [hh_tensor]
      _ = (h.rTensor N) ((((F.map (homOfLE hik)).hom).rTensor N) x) := rfl
      _ = 0 := by rw [hx_zero, LinearMap.map_zero]
  simpa [LinearMap.mem_ker] using hcolim_zero

/-- Helper for Proposition 10.88.6: after fixing a bundled test object `N`, tensoring the stage
factorization of the colimit map yields a literal composite factorization of tensor maps. -/
lemma colimit_map_transition_rTensor_comp_eq
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i k : I} (hik : i ≤ k)
    (N : ModuleCat.{max v w} R) :
    ∃ h : F.obj k →ₗ[R] M,
      (((colimit.ι F i ≫ c.hom).hom).rTensor N) =
        (h.rTensor N).comp (((F.map (homOfLE hik)).hom).rTensor N) := by
  rcases colimit_map_factors_through_transition_hom (R := R) (F := F) (c := c) hik with ⟨h, hh⟩
  refine ⟨h, ?_⟩
  -- Route correction: freeze the bundled test object `N` and tensor the explicit factorization,
  -- instead of specializing the polymorphic `.Dominates` API.
  -- Proof comment: tensoring preserves composition, so the linear-map factorization lifts directly
  -- to the corresponding tensor maps.
  simpa [LinearMap.rTensor_comp] using
    congrArg (fun t : F.obj i →ₗ[R] M ↦ t.rTensor N) hh

/-- Helper for Proposition 10.88.6: if the later transition map kills a tensor element, then the
tensorized colimit map kills the same element on the same bundled test object. -/
lemma colimit_map_transition_zero_of_mem_ker_moduleCat
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i k : I} (hik : i ≤ k)
    (N : ModuleCat.{max v w} R)
    {x : (F.obj i : Type (max v w)) ⊗[R] (N : Type (max v w))}
    (hx : x ∈ LinearMap.ker (((F.map (homOfLE hik)).hom).rTensor N)) :
    (((colimit.ι F i ≫ c.hom).hom).rTensor N) x = 0 := by
  rcases colimit_map_transition_rTensor_comp_eq (R := R) (F := F) (c := c) hik N with ⟨h, hh_tensor⟩
  have hx_zero : (((F.map (homOfLE hik)).hom).rTensor N) x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  -- Proof comment: rewrite the tensorized colimit map using the fixed-`N` factorization and then
  -- push the vanishing of the transition tensor map through the postcomposition.
  calc
    (((colimit.ι F i ≫ c.hom).hom).rTensor N) x
        = ((h.rTensor N).comp (((F.map (homOfLE hik)).hom).rTensor N)) x := by
            rw [hh_tensor]
    _ = (h.rTensor N) ((((F.map (homOfLE hik)).hom).rTensor N) x) := rfl
    _ = 0 := by rw [hx_zero, LinearMap.map_zero]

/-- Helper for Proposition 10.88.6: on any bundled test object, the domination of the colimit leg
over a later transition map gives the corresponding tensor-kernel inclusion. -/
lemma colimit_map_transition_kernel_le_moduleCat
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i k : I} (hik : i ≤ k)
    (N : ModuleCat.{max v w} R) :
    LinearMap.ker (((F.map (homOfLE hik)).hom).rTensor N) ≤
      LinearMap.ker (((colimit.ι F i ≫ c.hom).hom).rTensor N) := by
  -- Route correction: prove the kernel inclusion directly on the fixed bundled test object `N`
  -- instead of routing through the polymorphic `.Dominates` specialization.
  intro x hx
  -- Proof comment: kernel membership is the vanishing statement for the tensorized transition map,
  -- and the previous helper propagates that vanishing to the tensorized colimit map.
  simpa [LinearMap.mem_ker] using
    colimit_map_transition_zero_of_mem_ker_moduleCat
      (R := R) (F := F) (c := c) hik N hx

/-- Helper for Proposition 10.88.6: once a map into the colimit factors through stage `i`, the
same map also factors through every later stage `j ≥ i` by composing with the transition map. -/
lemma push_forward_stage_factorization
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {P : ModuleCat.{max v w} R}
    {i j : I}
    (g : P ⟶ F.obj i)
    (f : P →ₗ[R] M)
    (hg : g ≫ (colimit.ι F i ≫ c.hom) = ModuleCat.ofHom f)
    (hij : i ≤ j) :
    g ≫ F.map (homOfLE hij) ≫ (colimit.ι F j ≫ c.hom) = ModuleCat.ofHom f := by
  -- Pushing the chosen stage factorization forward along `f_{ij}` preserves the colimit
  -- composite because the colimit cocone is compatible with every transition map.
  calc
    g ≫ F.map (homOfLE hij) ≫ (colimit.ι F j ≫ c.hom)
        = g ≫ (F.map (homOfLE hij) ≫ colimit.ι F j) ≫ c.hom := by
            simp [Category.assoc]
    _ = g ≫ colimit.ι F i ≫ c.hom := by
            simpa [Category.assoc] using
              congrArg (fun t ↦ g ≫ t ≫ c.hom) (colimit.w F (homOfLE hij))
    _ = ModuleCat.ofHom f := by
            simpa [Category.assoc] using hg

/-- Helper for Proposition 10.88.6: forgetting the pushed-forward stage factorization yields the
expected equality of underlying linear maps at the later stage. -/
lemma pushed_forward_stage_factorization_hom_eq
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {P : ModuleCat.{max v w} R}
    {i j : I}
    (g : P ⟶ F.obj i)
    (f : P →ₗ[R] M)
    (hg : g ≫ (colimit.ι F i ≫ c.hom) = ModuleCat.ofHom f)
    (hij : i ≤ j) :
    (g ≫ F.map (homOfLE hij) ≫ (colimit.ι F j ≫ c.hom)).hom = f := by
  -- Proof comment: first push the factorization forward categorically, then forget the bundled
  -- equality to the underlying linear map.
  exact
    stage_factorization_hom_eq
      (R := R)
      (F := F)
      (c := c)
      (g₀ := g ≫ F.map (homOfLE hij))
      (f := f)
      (push_forward_stage_factorization (R := R) (F := F) (c := c) (g := g) (f := f) hg hij)

/-- Helper for Proposition 10.88.6: a displayed factorization with explicit factor map already
gives the corresponding domination relation. -/
lemma dominates_of_explicit_factorization
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (h : B →ₗ[R] C)
    (hh : g = ((h.comp f) : A →ₗ[R] C)) :
    g.Dominates f := by
  subst hh
  -- Proof comment: after rewriting `g` as the explicit composite `h.comp f`, tensoring preserves
  -- that factorization and the kernel inclusion is immediate.
  intro N
  intro _ _
  simpa [LinearMap.rTensor_comp] using
    LinearMap.ker_le_ker_comp (f.rTensor N) (h.rTensor N)

/-- Helper for Proposition 10.88.6: on pure tensors, an explicit pointwise factorization of `g`
through `f` and `h` gives the corresponding formula after right-tensoring. -/
lemma rTensor_tmul_of_explicit_factorization
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {N : Type (max u v w)} [AddCommMonoid N] [Module R N]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C} (h : B →ₗ[R] C)
    (hh : ∀ x, g x = h (f x))
    (a : A) (n : N) :
    (g.rTensor N) (a ⊗ₜ[R] n) = (h.rTensor N) ((f.rTensor N) (a ⊗ₜ[R] n)) := by
  -- Proof comment: evaluate both tensor maps on a pure tensor and use the pointwise factorization
  -- hypothesis on the source element `a`.
  simp [LinearMap.rTensor_tmul, hh a]

/-- Helper for Proposition 10.88.6: an explicit factorization transports tensor vanishing from the
intermediate map to the factored map. -/
lemma tensor_zero_of_explicit_factorization
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {N : Type (max u v w)} [AddCommMonoid N] [Module R N]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C} (h : B →ₗ[R] C)
    (hh : g = ((h.comp f) : A →ₗ[R] C))
    {x : A ⊗[R] N}
    (hx : (f.rTensor N) x = 0) :
    (g.rTensor N) x = 0 := by
  -- Proof comment: after rewriting `g` as the displayed composite, tensoring preserves the
  -- factorization and the target vanishing follows by postcomposition with `h ⊗ 1`.
  subst hh
  calc
    ((h.comp f).rTensor N) x = (h.rTensor N) ((f.rTensor N) x) := by
      simp [LinearMap.rTensor_comp]
    _ = 0 := by rw [hx, LinearMap.map_zero]

/-- Helper for Proposition 10.88.6: if two right-tensor maps agree on a bundled test object, then
their kernels coincide on that bundled test object as well. -/
lemma LinearMap.ker_eq_of_rTensor_eq_moduleCat
    {A B : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    {f g : A →ₗ[R] B}
    (N : ModuleCat.{max v w} R)
    (hfg : f.rTensor N = g.rTensor N) :
    LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
  -- Proof comment: after rewriting the two tensor maps to be literally equal, their kernels agree
  -- definitionally on the bundled test object.
  simpa [hfg]

end
