import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.TFAE
import StacksProject_2024.Chap10.Definition_10_88_2
import StacksProject_2024.Chap10.Lemma_10_11_1
import StacksProject_2024.Chap10.Lemma_10_11_4
import StacksProject_2024.Chap10.Lemma_10_88_3
import StacksProject_2024.Chap10.Lemma_10_88_5
import StacksProject_2024.Chap10.Proposition_10_88_6.Index

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped TensorProduct

universe u v w

noncomputable section

section HomInverseSystem

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I]

/-- The inverse system `i ↦ Hom_R(M_i, N)` attached to a directed system of `R`-modules. -/
abbrev colimitPresentationHomInverseSystem
    (F : I ⥤ ModuleCat.{max v w} R) (N : ModuleCat.{max v w} R) :
    Iᵒᵖ ⥤ Type (max v w) :=
  F.op ⋙ preadditiveYoneda.obj N ⋙ forget AddCommGrpCat

end HomInverseSystem

section

variable {R : Type u} [CommRing R]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {M : Type (max v w)} [AddCommGroup M] [Module R M]

/-- Helper for Proposition 10.88.6: if `g` factors through `f`, then `g` dominates `f`. -/
lemma dominates_of_factorization
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (hfac : ∃ h : B →ₗ[R] C, g = h.comp f) :
    g.Dominates f := by
  rcases hfac with ⟨h, rfl⟩
  intro Q
  intro _ _
  -- Tensoring preserves the displayed factorization, so the kernel inclusion is immediate.
  simpa [LinearMap.rTensor_comp] using
    LinearMap.ker_le_ker_comp (f.rTensor Q) (h.rTensor Q)

/-- Helper for Proposition 10.88.6: domination is stable under precomposition. -/
lemma dominates_comp_right
    {A A' B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup A'] [Module R A']
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C} {u : A' →ₗ[R] A}
    (hdom : g.Dominates f) :
    (g.comp u).Dominates (f.comp u) := by
  intro Q
  intro _ _
  intro x hx
  -- After rewriting the tensor of a composite, the claim reduces to the original domination.
  have hx' : (u.rTensor Q) x ∈ LinearMap.ker (f.rTensor Q) := by
    simpa [LinearMap.mem_ker, LinearMap.rTensor_comp] using hx
  have hx'' : (u.rTensor Q) x ∈ LinearMap.ker (g.rTensor Q) := hdom Q hx'
  simpa [LinearMap.mem_ker, LinearMap.rTensor_comp] using hx''

/-- Helper for Proposition 10.88.6: domination is a transitive relation. -/
lemma dominates_trans
    {A B C D : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    [AddCommGroup D] [Module R D]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C} {h : A →ₗ[R] D}
    (hhg : h.Dominates g) (hgf : g.Dominates f) :
    h.Dominates f := by
  intro Q
  intro _ _
  intro x hx
  exact hhg Q (hgf Q hx)

/-- Helper for Proposition 10.88.6: mutual domination is exactly the kernel equality needed in
clause `(1)` once a test module is fixed. -/
lemma tensor_kernel_eq_of_mutual_domination
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (hgf : g.Dominates f) (hfg : f.Dominates g)
    (N : Type (max u v w)) [AddCommMonoid N] [Module R N] :
    LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
  -- Proof comment: the two domination inclusions are exactly the two inequalities needed for
  -- antisymmetry of the tensor kernels.
  exact le_antisymm (hgf N) (hfg N)

/-- Helper for Proposition 10.88.6: equality of all tensor kernels implies domination. -/
lemma dominates_of_tensor_kernel_eq
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (hker : ∀ (N : Type (max u v w)) [AddCommMonoid N] [Module R N],
      LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) :
    g.Dominates f := by
  intro N _ _
  -- Rewriting the source kernel with the assumed equality turns the goal into the identity
  -- inclusion.
  simpa [hker N]

/-- Helper for Proposition 10.88.6: the cokernel of a map between finitely presented modules is
again finitely presented. -/
lemma finitePresentation_cokernel_of_finitePresentation_map
    {A B : ModuleCat.{max v w} R}
    [Module.FinitePresentation R A] [Module.FinitePresentation R B]
    (f : A →ₗ[R] B) :
    Module.FinitePresentation R (B ⧸ LinearMap.range f) := by
  letI : Module.Finite R A := inferInstance
  have hfg : (LinearMap.range f).FG := Submodule.fg_range f
  -- The quotient map is surjective, and its kernel is exactly the finitely generated range.
  exact Module.finitePresentation_of_surjective (LinearMap.range f).mkQ
    (Submodule.mkQ_surjective _) <| by
      simpa [Submodule.ker_mkQ] using hfg

/-- Helper for Proposition 10.88.6: finite presentation transfers across a ring equivalence by
restricting scalars along that equivalence. -/
lemma module_finitePresentation_compHom_of_ringEquiv
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    {N : Type*} [AddCommGroup N] [Module B N] [Module.FinitePresentation B N] :
    let _ : Algebra A B := e.toRingHom.toAlgebra
    let _ : Module A N := Module.compHom N e.toRingHom
    let _ : IsScalarTower A B N := RestrictScalars.isScalarTower A B N
    Module.FinitePresentation A N := by
  let _ : Algebra A B := e.toRingHom.toAlgebra
  let _ : Module A N := Module.compHom N e.toRingHom
  let _ : IsScalarTower A B N := RestrictScalars.isScalarTower A B N
  have hB : Module.FinitePresentation A B := by
    -- Proof comment: via the ring equivalence, `B` is just the free rank-one `A`-module.
    exact Module.FinitePresentation.of_equiv (Module.compHom.toLinearEquiv e)
  -- Proof comment: once `B` is finitely presented over `A`, transitivity upgrades finite
  -- presentation of `N` over `B` to finite presentation over `A`.
  exact Module.FinitePresentation.trans (R := A) (S := B) (M := N)

/-- Helper for Proposition 10.88.6: reinterpret an `R`-linear map as a linear map over the lifted
scalar ring `ULift R`. -/
def LinearMap.over_ulift_ring
    {A B : Type (max u v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) :
    A →ₗ[ULift.{max v w} R] B where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    -- Proof comment: the lifted scalar action is defined by `ULift.down`, so `R`-linearity of
    -- `f` immediately gives linearity over `ULift R`.
    simpa [ULift.smul_def] using f.map_smul r.down x

/-- Helper for Proposition 10.88.6: forget the lifted scalar ring on a linear map over `ULift R`.
-/
def LinearMap.from_ulift_ring
    {A B : Type (max u v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (f : A →ₗ[ULift.{max v w} R] B) :
    A →ₗ[R] B where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    -- Proof comment: `R` acts through `ULift.up`, so linearity over `ULift R` restricts back to
    -- ordinary `R`-linearity.
    simpa using f.map_smul (ULift.up r) x

/-- Helper for Proposition 10.88.6: finite presentation over `R` transfers to the lifted scalar
ring `ULift R`. -/
lemma module_finitePresentation_over_ulift_ring_of_finitePresentation
    {N : Type*} [AddCommGroup N] [Module R N] [Module.FinitePresentation R N] :
    Module.FinitePresentation (ULift.{max v w} R) N := by
  -- Proof comment: specialize the ring-equivalence transfer to `ULift.ringEquiv`.
  simpa using
    (module_finitePresentation_compHom_of_ringEquiv
      (e := (ULift.ringEquiv : ULift.{max v w} R ≃+* R))
      (N := N))

/-- Helper for Proposition 10.88.6: a displayed factorization still implies domination in the
ambient module universe `max v w`. -/
lemma LinearMap.dominates_of_displayed_factorization_mixedUniverse
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (h : B →ₗ[R] C) (hg : ∀ x, g x = h (f x)) :
    g.Dominates f := by
  intro Q
  intro _ _
  intro x hx
  have hTensor :
      g.rTensor Q = ((h.rTensor Q).comp (f.rTensor Q) : A ⊗[R] Q →ₗ[R] C ⊗[R] Q) := by
    ext a q
    simp [LinearMap.rTensor_tmul, hg a]
  have hx0 : (f.rTensor Q) x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  calc
    (g.rTensor Q) x = ((h.rTensor Q).comp (f.rTensor Q)) x := by rw [hTensor]
    _ = (h.rTensor Q) ((f.rTensor Q) x) := rfl
    _ = 0 := by rw [hx0, LinearMap.map_zero]

/-- Helper for Proposition 10.88.6: the domination-to-factorization criterion from Lemma
`10.88.5` also works in the ambient module universe `max v w`. -/
theorem LinearMap.dominates_iff_factorsThrough_of_finitePresentation_cokernel_mixedUniverse
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : A →ₗ[R] C)
    [Module.FinitePresentation R (B ⧸ LinearMap.range f)] :
    g.Dominates f ↔ ∃ h : B →ₗ[R] C, g = ((h.comp f) : A →ₗ[R] C) := by
  constructor
  · intro hdom
    -- Route correction: the forward implication still needs the missing bundled same-universe
    -- factorization owner below.
    -- TODO: once the bundled owner is repaired, this becomes a short bundling corollary.
    sorry
  · rintro ⟨h, rfl⟩
    intro Q
    intro _ _
    -- Proof comment: tensoring preserves the displayed factorization, so the kernel inclusion is
    -- immediate.
    simpa [LinearMap.rTensor_comp] using
      LinearMap.ker_le_ker_comp (f.rTensor Q) (h.rTensor Q)

/-- Helper for Proposition 10.88.6: a same-universe kernel inclusion hypothesis on bundled
`ModuleCat` morphisms already gives the factorization conclusion from Lemma `10.88.5`. -/
theorem moduleCat_hom_factorsThrough_of_same_universe_kernel_le_of_finitePresentation_cokernel
    {A B C : ModuleCat.{max v w} R}
    (f : A ⟶ B) (g : A ⟶ C)
    [Module.FinitePresentation R (B ⧸ LinearMap.range f.hom)]
    (hker : ∀ (Q : Type (max v w)) [AddCommGroup Q] [Module R Q],
      LinearMap.ker (f.hom.rTensor Q) ≤ LinearMap.ker (g.hom.rTensor Q)) :
    ∃ h : B ⟶ C, g = f ≫ h := by
  -- Route correction: the right owner for this theorem is the pushout proof in the fixed object
  -- universe `max v w`, but that proof still needs a clean bridge from the same-universe kernel
  -- hypothesis here to the split criterion for short complexes after lifting scalars.
  -- TODO: replay Lemma `10.88.5` over `ULift R` inside `ModuleCat.{max v w}`, transfer finite
  -- presentation of the cokernel across `ULift.ringEquiv`, and then descend the resulting
  -- factorization back to `R`.
  sorry

/-- Helper for Proposition 10.88.6: a domination hypothesis on bundled `ModuleCat` morphisms
forces a factorization once the cokernel of the first map is finitely presented. -/
theorem moduleCat_hom_factorsThrough_of_dominates_of_finitePresentation_cokernel
    {A B C : ModuleCat.{max v w} R}
    (f : A ⟶ B) (g : A ⟶ C)
    [Module.FinitePresentation R (B ⧸ LinearMap.range f.hom)]
    (hdom : g.hom.Dominates f.hom) :
    ∃ h : B ⟶ C, g = f ≫ h := by
  -- Route correction: the bundled wrapper still needs an elaboration-stable way to specialize the
  -- mixed-universe linear-map factorization theorem on the underlying carriers.
  -- TODO: pin the `ModuleCat.{max v w}` object universe at the theorem application site so the
  -- resulting linear-map factorization can be repackaged as a bundled morphism.
  sorry

/-- Helper for Proposition 10.88.6: equality of tensor kernels on bundled `ModuleCat` test modules
already gives the corresponding factorization once the cokernel of the first map is finitely
presented. -/
theorem moduleCat_hom_factorsThrough_of_tensor_kernel_eq_of_finitePresentation_cokernel
    {A B C : ModuleCat.{max v w} R}
    (f : A ⟶ B) (g : A ⟶ C)
    [Module.FinitePresentation R (B ⧸ LinearMap.range f.hom)]
    (hker : ∀ N : ModuleCat.{max v w} R,
      LinearMap.ker (f.hom.rTensor N) = LinearMap.ker (g.hom.rTensor N)) :
    ∃ h : B ⟶ C, g = f ≫ h := by
  -- Route correction: this bundled equality wrapper is downstream from the same-universe bundled
  -- owner, so keeping it local avoids reintroducing the same universe-elaboration loop.
  -- TODO: convert `hker` to the kernel-inclusion hypothesis expected by the previous theorem once
  -- that theorem elaborates stably.
  sorry

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

/-- Helper for Proposition 10.88.6: a map from a finitely presented module into the colimit
presentation factors through one stage. -/
lemma finite_presentation_factor_through_filtered_colimit_stage
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    (P : ModuleCat.{max v w} R)
    [Module.FinitePresentation R P]
    (f : P ⟶ ModuleCat.of R M) :
    ∃ (i : I) (g : P ⟶ F.obj i), g ≫ (colimit.ι F i ≫ c.hom) = f := by
  -- Lift the index to the common universe and apply the finitely presentable owner there.
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
  -- Lift the index to the common universe, then descend the returned later-stage equality.
  exact ulift_index_eventually_equal_of_hom_to_colimit_of_finite_module
    (R := R) (F := F) (i := j) u v h

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

/-- Helper for Proposition 10.88.6: if a transition map out of `i` dominates another transition
map out of `i`, then the first transition map factors through the second. -/
lemma transition_factorization_of_dominates_and_fp_cokernel
    (F : I ⥤ ModuleCat.{max v w} R)
    (hfp : ∀ i, Module.FinitePresentation R (F.obj i))
    {i j k : I} (hik : i ≤ k) (hij : i ≤ j)
    (hdom : ((F.map (homOfLE hij)).hom).Dominates ((F.map (homOfLE hik)).hom)) :
    ∃ h : F.obj k ⟶ F.obj j, F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h := by
  -- Route correction: this adapter should be a short specialization of the mixed-universe
  -- factorization theorem, but the current elaboration still loses the stage-object universe at
  -- the `ModuleCat` packaging step.
  -- TODO: package the stage objects explicitly in `ModuleCat.{max v w} R` when invoking the
  -- factorization owner, then rewrap the returned linear map as the desired morphism.
  sorry

/-- Helper for Proposition 10.88.6: the colimit object of `F` is equal to the bundled module on
its underlying carrier. -/
lemma colimit_eq_moduleCat_of_carrier
    (F : I ⥤ ModuleCat.{max v w} R) :
    colimit F =
      ModuleCat.of R ((colimit F : ModuleCat.{max v w} R) : Type (max v w)) := by
  -- Proof comment: `ModuleCat.of` is reducible on an already bundled module carrier.
  rfl

/-- Helper for Proposition 10.88.6: package the lifted-index cocone as a colimit presentation in
the common universe of the module stages. -/
noncomputable def lifted_index_colimitPresentation
    (F : I ⥤ ModuleCat.{max v w} R) :
    ColimitPresentation (ULift.{max v w} I)
      (ModuleCat.of R ((colimit F : ModuleCat.{max v w} R) : Type (max v w))) :=
  { diag := lifted_index_diagram (R := R) F
    ι :=
      (lifted_index_cocone (R := R)
        (M := ((colimit F : ModuleCat.{max v w} R) : Type (max v w)))
        F (eqToIso (colimit_eq_moduleCat_of_carrier (R := R) F))).ι
    isColimit :=
      common_universe_lifted_index_isColimit (R := R)
        (M := ((colimit F : ModuleCat.{max v w} R) : Type (max v w)))
        F (eqToIso (colimit_eq_moduleCat_of_carrier (R := R) F)) }

/-- Helper for Proposition 10.88.6: if an element dies after tensoring with the colimit map, then
it already dies after tensoring with a later transition map. -/
lemma tensor_kernel_eventually_zero_of_colimit_zero
    (F : I ⥤ ModuleCat.{max v w} R)
    {i : I}
    {N : Type (max u v w)} [AddCommGroup N] [Module R N]
    {x : F.obj i ⊗[R] N}
    (hx : (((colimit.ι F i).hom).rTensor N) x = 0) :
    ∃ (k : I) (hik : i ≤ k), (((F.map (homOfLE hik)).hom).rTensor N) x = 0 := by
  -- Route correction: the proof reduces to the left-tensor stabilization lemma from
  -- `Lemma 10.88.3`, but that owner is currently only available in the equal-universe setting.
  -- TODO: add the mixed-universe lift of `exists_later_stage_lTensor_eq_zero`, commute `rTensor`
  -- to `lTensor`, apply the lifted owner, and commute back.
  sorry

/-- Helper for Proposition 10.88.6: tensor vanishing after the identified colimit map already
vanishes before postcomposing with the colimit isomorphism. -/
lemma tensor_zero_of_iso_comp_colimit_zero
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i : I}
    {N : Type (max u v w)} [AddCommGroup N] [Module R N]
    {x : F.obj i ⊗[R] N}
    (hx : (((colimit.ι F i ≫ c.hom).hom).rTensor N) x = 0) :
    (((colimit.ι F i).hom).rTensor N) x = 0 := by
  have hcolim_iso : colimit.ι F i = colimit.ι F i ≫ c.hom ≫ c.inv := by
    -- Compose `colimit.ι F i` with the identity `c.hom ≫ c.inv = 𝟙` on the colimit object.
    calc
      colimit.ι F i = colimit.ι F i ≫ 𝟙 (colimit F) := by simp
      _ = colimit.ι F i ≫ (c.hom ≫ c.inv) := by rw [c.hom_inv_id]
      _ = colimit.ι F i ≫ c.hom ≫ c.inv := by simp
  have hcolim_tensor :
      (((colimit.ι F i).hom).rTensor N) x =
        (((colimit.ι F i ≫ c.hom ≫ c.inv).hom).rTensor N) x := by
    -- Evaluate the morphism identity above after tensoring with `N`.
    simpa using congrArg
      (fun t : F.obj i ⟶ colimit F ↦ (t.hom.rTensor N) x) hcolim_iso
  have hcolim_apply :
      (LinearMap.rTensor N (c.inv.hom.comp ((colimit.ι F i ≫ c.hom).hom))) x =
        (c.inv.hom.rTensor N) ((((colimit.ι F i ≫ c.hom).hom).rTensor N) x) := by
    -- Tensoring a composite is the composite of the tensor maps.
    simpa only [LinearMap.rTensor_comp] using
      (LinearMap.rTensor_comp_apply (M := N) (f := (colimit.ι F i ≫ c.hom).hom)
        (g := c.inv.hom) (x := x))
  calc
    (((colimit.ι F i).hom).rTensor N) x
        = (((colimit.ι F i ≫ c.hom ≫ c.inv).hom).rTensor N) x := hcolim_tensor
    _ = (LinearMap.rTensor N (c.inv.hom.comp ((colimit.ι F i ≫ c.hom).hom))) x := by
          rfl
    _ = (c.inv.hom.rTensor N) ((((colimit.ι F i ≫ c.hom).hom).rTensor N) x) := hcolim_apply
    _ = 0 := by rw [hx]; simp only [LinearMap.map_zero]

/-- Helper for Proposition 10.88.6: if a later transition map kills a tensor element, then any
transition map factoring through it kills the same tensor element. -/
lemma tensor_zero_of_transition_factorization
    (F : I ⥤ ModuleCat.{max v w} R)
    {i j k : I} {hij : i ≤ j} {hik : i ≤ k}
    {N : Type (max u v w)} [AddCommGroup N] [Module R N]
    {x : F.obj i ⊗[R] N}
    {h : F.obj k ⟶ F.obj j}
    (hh : F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h)
    (hx : (((F.map (homOfLE hik)).hom).rTensor N) x = 0) :
    (((F.map (homOfLE hij)).hom).rTensor N) x = 0 := by
  have hh_tensor :
      (((F.map (homOfLE hij)).hom).rTensor N) x =
        ((((F.map (homOfLE hik) ≫ h).hom).rTensor N) x) := by
    -- Evaluate the factorization identity after tensoring with `N`.
    simpa using congrArg (fun t : F.obj i ⟶ F.obj j ↦ (t.hom.rTensor N) x) hh
  have hh_apply :
      ((((F.map (homOfLE hik) ≫ h).hom).rTensor N) x) =
        (h.hom.rTensor N) ((((F.map (homOfLE hik)).hom).rTensor N) x) := by
    -- Tensoring the factored map converts the target to a postcomposition of the later-stage map.
    change (LinearMap.rTensor N (h.hom.comp (F.map (homOfLE hik)).hom)) x =
      (h.hom.rTensor N) ((((F.map (homOfLE hik)).hom).rTensor N) x)
    simpa only [LinearMap.rTensor_comp] using
      (LinearMap.rTensor_comp_apply (M := N) (f := (F.map (homOfLE hik)).hom)
        (g := h.hom) (x := x))
  calc
    (((F.map (homOfLE hij)).hom).rTensor N) x
        = ((((F.map (homOfLE hik) ≫ h).hom).rTensor N) x) := hh_tensor
    _ = (h.hom.rTensor N) ((((F.map (homOfLE hik)).hom).rTensor N) x) := hh_apply
    _ = 0 := by rw [hx]; simp only [LinearMap.map_zero]

/-- Helper for Proposition 10.88.6: eventual tail factorization forces the chosen transition map
to dominate the map from the stage into the colimit. -/
lemma dominates_colimit_map_of_tail_factorization
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i j : I} (hij : i ≤ j)
    (hfactor : ∀ (k : I) (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj j,
      F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h) :
    ((F.map (homOfLE hij)).hom).Dominates ((colimit.ι F i ≫ c.hom).hom) := by
  intro N _ _
  letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R (M := N)
  intro x hx
  -- First remove the postcomposition by the chosen colimit isomorphism.
  have hx_iso :
      ((((colimit.ι F i ≫ c.hom).hom).rTensor N) x) = 0 := by
    simpa [LinearMap.mem_ker] using hx
  have hx_colim :
      (((colimit.ι F i).hom).rTensor N) x = 0 := by
    exact tensor_zero_of_iso_comp_colimit_zero
      (R := R) (F := F) (c := c) (x := x) hx_iso
  -- Next stabilize the vanishing at a later stage of the directed system.
  obtain ⟨k, hik, hxk⟩ :=
    tensor_kernel_eventually_zero_of_colimit_zero (R := R) (F := F) (x := x) hx_colim
  -- Finally use the assumed tail factorization to transport the vanishing back to stage `j`.
  obtain ⟨h, hh⟩ := hfactor k hik
  have hxj :
      (((F.map (homOfLE hij)).hom).rTensor N) x = 0 := by
    exact tensor_zero_of_transition_factorization (R := R) (F := F) (hh := hh) hxk
  simpa [LinearMap.mem_ker] using hxj

/-- Helper for Proposition 10.88.6: the product-target Mittag-Leffler condition yields the
eventual factorization condition on transition maps. -/
lemma product_hom_mittag_leffler_gives_stage_factorization
    (F : I ⥤ ModuleCat.{max v w} R)
    (hML : (colimitPresentationHomInverseSystem F
      (ModuleCat.of R ((s : I) → F.obj s))).IsMittagLeffler) :
    ∀ i : I, ∃ (j : I) (hij : i ≤ j),
      ∀ (k : I) (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj j,
        F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h := by
  classical
  intro i
  let G := colimitPresentationHomInverseSystem F (ModuleCat.of R ((s : I) → F.obj s))
  obtain ⟨jop, f, hf⟩ := (Functor.isMittagLeffler_iff_subset_range_comp G).mp hML (op i)
  let j := unop jop
  have hij : i ≤ j := leOfHom f.unop
  let insj : F.obj j ⟶ ModuleCat.of R ((s : I) → F.obj s) :=
    ModuleCat.ofHom (LinearMap.single R (fun s : I ↦ F.obj s) j)
  let projj : ModuleCat.of R ((s : I) → F.obj s) ⟶ F.obj j :=
    ModuleCat.ofHom (LinearMap.proj j)
  have hins_proj : insj ≫ projj = 𝟙 (F.obj j) := by
    apply ModuleCat.hom_ext
    ext x
    simp [insj, projj]
  refine ⟨j, hij, ?_⟩
  intro k hik
  obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
  have hil : i ≤ l := hij.trans hjl
  have hf_unop : f.unop = homOfLE hij := Subsingleton.elim _ _
  have hsubset :
      Set.range (fun g : F.obj j ⟶ ModuleCat.of R ((s : I) → F.obj s) ↦
        F.map (homOfLE hij) ≫ g) ⊆
        Set.range (fun g : F.obj l ⟶ ModuleCat.of R ((s : I) → F.obj s) ↦
          F.map (homOfLE hil) ≫ g) := by
    simpa [G, hf_unop] using hf ((homOfLE hjl).op)
  have hmem :
      F.map (homOfLE hij) ≫ insj ∈
        Set.range (fun g : F.obj j ⟶ ModuleCat.of R ((s : I) → F.obj s) ↦
          F.map (homOfLE hij) ≫ g) := by
    exact ⟨insj, rfl⟩
  obtain ⟨gl, hgl⟩ := hsubset hmem
  refine ⟨F.map (homOfLE hkl) ≫ gl ≫ projj, ?_⟩
  -- Project the stabilized product-valued factorization to the `j`-th coordinate.
  calc
    F.map (homOfLE hij)
        = ((F.map (homOfLE hij) ≫ insj) ≫ projj) := by simp [Category.assoc, hins_proj]
    _ = ((F.map (homOfLE hil) ≫ gl) ≫ projj) := by
          simpa [Category.assoc] using congrArg (fun t ↦ t ≫ projj) hgl.symm
    _ = ((F.map (homOfLE hik) ≫ F.map (homOfLE hkl)) ≫ gl) ≫ projj := by
          have hcomp : homOfLE hil = homOfLE hik ≫ homOfLE hkl := Subsingleton.elim _ _
          rw [← Functor.map_comp, hcomp, Category.assoc]
    _ = F.map (homOfLE hik) ≫ (F.map (homOfLE hkl) ≫ gl ≫ projj) := by
          simp [Category.assoc]

-- Proof sketch: prove `(1) ↔ (2)` by factoring a finitely presented target through a stage of the
-- colimit and using the domination-to-factorization criterion with finitely presented cokernel;
-- prove `(2) ↔ (3)` by the same criterion applied to the transition maps; `(3) → (4) → (5)` is
-- immediate from the definition of Mittag-Leffler for the Hom inverse systems; and `(5) → (3)` is
-- obtained by evaluating eventual image stabilization on the product module `∏ s, M_s` and then on
-- the `j`-th projection.
/-- Proposition 10.88.6: for a directed system `F` of finitely presented `R`-modules with colimit
`M`, the five standard domination, factorization, and Hom-Mittag-Leffler conditions on the
presentation are equivalent. -/
theorem directed_colimit_presentation_mittag_leffler_tfae
    (F : I ⥤ ModuleCat.{max v w} R)
    (hfp : ∀ i, Module.FinitePresentation R (F.obj i))
    (c : colimit F ≅ ModuleCat.of R M) :
    List.TFAE
      [ (∀ (P : ModuleCat.{max v w} R) [Module.FinitePresentation R P] (f : P →ₗ[R] M),
            ∃ (Q : ModuleCat.{max v w} R) (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q),
              ∀ N : ModuleCat.{max v w} R,
                LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)),
        (∀ i : I, ∃ (j : I) (hij : i ≤ j),
            ((F.map (homOfLE hij)).hom).Dominates ((colimit.ι F i ≫ c.hom).hom)),
        (∀ i : I, ∃ (j : I) (hij : i ≤ j),
            ∀ (k : I) (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj j,
              F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h),
        (∀ N : ModuleCat.{max v w} R, (colimitPresentationHomInverseSystem F N).IsMittagLeffler),
        (colimitPresentationHomInverseSystem F
            (ModuleCat.of R ((s : I) → F.obj s))).IsMittagLeffler ] := by
  classical
  tfae_have 1 → 2 := by
    -- Route correction: the source-faithful proof skeleton is in place, but the first factorized
    -- target `Q` still loses its object universe when we instantiate the clause `(1)` witness.
    -- TODO: package the clause `(1)` witness as an explicit `ModuleCat.{max v w} R`, then replay
    -- the existing factorization/stabilization chain.
    sorry
  tfae_have 2 → 1 := by
    -- Route correction: the precomposition argument is correct, but the current stage-factorization
    -- owner still loses the source object universe when instantiated inside this TFAE branch.
    -- TODO: once that wrapper elaborates stably, use `tensor_kernel_eq_of_mutual_domination` to
    -- package the two precomposed domination relations into clause `(1)`.
    sorry
  tfae_have 2 → 3 := by
    intro h₂
    intro i
    obtain ⟨j, hij, hdom⟩ := h₂ i
    refine ⟨j, hij, ?_⟩
    intro k
    intro hik
    -- Proof comment: the chosen transition map dominates the colimit map, and the colimit map in
    -- turn dominates every later transition out of stage `i`.
    have hcolim_dom :
        ((colimit.ι F i ≫ c.hom).hom).Dominates ((F.map (homOfLE hik)).hom) :=
      colimit_map_dominates_transition (R := R) (F := F) (c := c) hik
    have htrans_dom :
        ((F.map (homOfLE hij)).hom).Dominates ((F.map (homOfLE hik)).hom) := by
      intro N
      intro _ _
      intro x hx
      exact hdom N (hcolim_dom N hx)
    -- Lemma `10.88.5` on the transition maps now yields the required factorization.
    exact transition_factorization_of_dominates_and_fp_cokernel
      (R := R) (F := F) (hfp := hfp) hik hij htrans_dom
  tfae_have 3 → 2 := by
    intro h₃
    intro i
    -- The source proof packages `(3) → (2)` into the local domination helper above.
    obtain ⟨j, hij, hj⟩ := h₃ i
    refine ⟨j, hij, ?_⟩
    exact dominates_colimit_map_of_tail_factorization (R := R) (F := F) (c := c) hij hj
  tfae_have 3 → 4 := by
    intro h₃
    intro (N : ModuleCat.{max v w} R)
    let G : Iᵒᵖ ⥤ Type (max v w) := colimitPresentationHomInverseSystem F N
    rw [Functor.isMittagLeffler_iff_subset_range_comp]
    intro iop
    let i : I := unop iop
    obtain ⟨j, hij, hj⟩ := h₃ i
    refine ⟨op j, (homOfLE hij).op, ?_⟩
    intro kop g
    let k : I := unop kop
    let hjk : j ≤ k := leOfHom g.unop
    let hik : i ≤ k := hij.trans hjk
    have hg_unop : g.unop = homOfLE hjk := Subsingleton.elim _ _
    have hcomp_unop :
        (g ≫ (homOfLE hij).op).unop = homOfLE hik := by
      -- In the thin category attached to the preorder, every arrow is the canonical `homOfLE`.
      exact Subsingleton.elim _ _
    have hjk_factor := hj k hik
    intro y hy
    have hy' :
        y ∈ Set.range (fun φ : F.obj j ⟶ (N : ModuleCat.{max v w} R) ↦ F.map (homOfLE hij) ≫ φ) := by
      simpa [G] using hy
    rcases hy' with ⟨φ, rfl⟩
    rcases hjk_factor with ⟨h, hh⟩
    have hyk :
        F.map (homOfLE hij) ≫ φ = F.map (homOfLE hik) ≫ (h ≫ φ) := by
      -- Precomposing with the factorization map realizes the stabilized range element at stage `k`.
      simpa [Category.assoc] using congrArg (fun t ↦ t ≫ φ) hh
    have hyk' :
        F.map (homOfLE hij) ≫ φ ∈
          Set.range
            (fun ψ : F.obj k ⟶ (N : ModuleCat.{max v w} R) ↦ F.map (homOfLE hik) ≫ ψ) := by
      exact ⟨h ≫ φ, hyk.symm⟩
    simpa [G, hg_unop, hcomp_unop] using hyk'
  tfae_have 4 → 5 := by
    intro h₄
    exact h₄ (ModuleCat.of R ((s : I) → F.obj s))
  tfae_have 5 → 3 := by
    intro h₅
    -- The product-target helper is exactly the source proof's coordinatewise extraction.
    exact product_hom_mittag_leffler_gives_stage_factorization (R := R) (F := F) h₅
  tfae_finish

end
