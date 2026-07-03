import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_10_88_6 (from Chap10) -/
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

/-! ### Definition_10_88_7 (from Chap10) -/
open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace Module

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A directed colimit presentation of an `R`-module by a Mittag-Leffler directed system. -/
structure MittagLefflerPresentation (R : Type u) (M : Type v) [Ring R] [AddCommGroup M]
    [Module R M] where
  index : Type v
  indexPreorder : Preorder index
  indexNonempty : Nonempty index
  indexDirected : IsDirectedOrder index
  diagram : index ⥤ ModuleCat R
  presentation_isMittagLeffler : @IsMittagLefflerDirectedSystem R _ index indexPreorder
    indexNonempty indexDirected diagram
  colimitIso : Nonempty (colimit diagram ≅ ModuleCat.of R M)

/-- Definition 10.88.7: an `R`-module `M` is Mittag-Leffler when it is the colimit of a directed
system satisfying `IsMittagLefflerDirectedSystem`. -/
class MittagLeffler (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M] where
  exists_presentation : Nonempty (MittagLefflerPresentation R M)

-- Proof sketch: take the constant one-object directed system on `M`. Finite presentation gives the
-- stagewise hypothesis, the colimit is `M` itself, and the unique transition maps satisfy the
-- factorization condition tautologically.
/-- A finitely presented module is Mittag-Leffler. -/
instance instMittagLefflerOfFinitePresentation
    [Module.FinitePresentation R M] : MittagLeffler R M := sorry

end

end Module

/-! ### Remark_10_88_8 (from Chap10) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u

namespace Module

section

variable {R : Type u} [CommRing R]
variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {M : Type u} [AddCommGroup M] [Module R M]

/- Domain triage:
- primary domain: Mittag-Leffler criteria for directed colimit presentations of modules;
- sampled owner declarations of the same kind:
  `Module.MittagLeffler`,
  `colimitPresentationHomInverseSystem`,
  `directed_colimit_presentation_mittag_leffler_tfae`,
  `TensorProduct.rTensorHomEquivHomRTensor`;
- owner abstraction: the chapter owner `Module.MittagLeffler`, with
  `directed_colimit_presentation_mittag_leffler_tfae` as the canonical presentation criterion;
- primitive data: the directed system `F`, its colimit identification `c`, the finite-free stage
  hypotheses, and the dual inverse-system Mittag-Leffler hypothesis;
- derived API: the source-facing bridge theorem below upgrading that dual hypothesis to
  `Module.MittagLeffler R M`.
-/
-- Proof sketch: start from the given finite free presentation and use the finite-free dual tensor-
-- Hom identification to promote the dual inverse-system Mittag-Leffler hypothesis to the universal
-- Hom inverse-system condition in Proposition `10.88.6`; the resulting presentation then witnesses
-- that `M` is Mittag-Leffler.
private theorem exists_factor_of_postcomp_range_subset
    [Nontrivial R]
    {A : Type u} [AddCommGroup A] [Module R A]
    {B : Type u} [AddCommGroup B] [Module R B]
    {C : Type u} [AddCommGroup C] [Module R C]
    [Module.Free R B] [Module.Finite R B]
    (u : A →ₗ[R] B) (v : A →ₗ[R] C)
    (h : Set.range (fun g : ModuleCat.of R B ⟶ ModuleCat.of R R ↦ ModuleCat.ofHom u ≫ g) ⊆
      Set.range (fun g : ModuleCat.of R C ⟶ ModuleCat.of R R ↦ ModuleCat.ofHom v ≫ g)) :
    ∃ w : C →ₗ[R] B, u = w.comp v := by
  classical
  let b : Module.Basis (Module.Free.ChooseBasisIndex R B) R B := Module.Free.chooseBasis R B
  letI : Finite (Module.Free.ChooseBasisIndex R B) := Module.Finite.finite_basis b
  choose ψ hψ using fun i ↦ h ⟨ModuleCat.ofHom (b.coord i), by rfl⟩
  let e : ((i : Module.Free.ChooseBasisIndex R B) → R) ≃ₗ[R] B := b.equivFun.symm
  let w : C →ₗ[R] B := e.toLinearMap.comp (LinearMap.pi fun i ↦ (ψ i).hom)
  refine ⟨w, ?_⟩
  ext a
  apply b.equivFun.injective
  ext i
  change b.coord i (u a) = b.coord i (e ((LinearMap.pi fun i ↦ (ψ i).hom) (v a)))
  rw [Module.Basis.coord_equivFun_symm]
  simpa [LinearMap.comp_apply] using
    congrArg (fun f : ModuleCat.of R A ⟶ ModuleCat.of R R ↦ f.hom a) (hψ i).symm

private theorem finite_free_dual_isMittagLeffler_gives_factorization
    [Nontrivial R]
    (F : I ⥤ ModuleCat R)
    (hfree : ∀ i, Module.Free R (F.obj i))
    (hfinite : ∀ i, Module.Finite R (F.obj i))
    (hdualML : (colimitPresentationHomInverseSystem F (ModuleCat.of R R)).IsMittagLeffler) :
    ∀ i : I, ∃ (j : I) (hij : i ≤ j),
      ∀ (k : I) (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj j,
        F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h := by
  intro i
  let G := colimitPresentationHomInverseSystem F (ModuleCat.of R R)
  obtain ⟨jop, f, hf⟩ := (Functor.isMittagLeffler_iff_subset_range_comp G).mp hdualML (op i)
  let j := unop jop
  have hij : i ≤ j := leOfHom f.unop
  refine ⟨j, hij, ?_⟩
  intro k hik
  obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
  have hil : i ≤ l := hij.trans hjl
  have hf_unop : f.unop = homOfLE hij := Subsingleton.elim _ _
  have hsubset :
      Set.range (fun g : F.obj j ⟶ ModuleCat.of R R ↦ F.map (homOfLE hij) ≫ g) ⊆
        Set.range (fun g : F.obj l ⟶ ModuleCat.of R R ↦ F.map (homOfLE hil) ≫ g) := by
    simpa [G, hf_unop] using hf (homOfLE hjl).op
  letI := hfree j
  letI := hfinite j
  obtain ⟨hl, hfac⟩ := exists_factor_of_postcomp_range_subset
    ((F.map (homOfLE hij)).hom) ((F.map (homOfLE hil)).hom) hsubset
  refine ⟨F.map (homOfLE hkl) ≫ ModuleCat.ofHom hl, ?_⟩
  calc
    F.map (homOfLE hij) = F.map (homOfLE hil) ≫ ModuleCat.ofHom hl := by
      apply ModuleCat.hom_ext
      exact hfac
    _ = F.map (homOfLE hik) ≫ (F.map (homOfLE hkl) ≫ ModuleCat.ofHom hl) := by
      have hcomp : homOfLE hil = homOfLE hik ≫ homOfLE hkl := Subsingleton.elim _ _
      rw [hcomp, Functor.map_comp, Category.assoc]

/-- Remark 10.88.8: for a directed colimit presentation of `M` by finite free `R`-modules, it is
sufficient that the inverse system of duals `i ↦ Hom_R(Mᵢ, R)` be Mittag-Leffler in order for `M`
to be Mittag-Leffler. -/
theorem mittagLeffler_of_finite_free_presentation_of_dual_isMittagLeffler
    (F : I ⥤ ModuleCat R)
    (c : colimit F ≅ ModuleCat.of R M)
    (hfree : ∀ i, Module.Free R (F.obj i))
    (hfinite : ∀ i, Module.Finite R (F.obj i))
    (hdualML : (colimitPresentationHomInverseSystem F (ModuleCat.of R R)).IsMittagLeffler) :
    MittagLeffler R M := by
  classical
  by_cases hR : Nontrivial R
  · letI := hR
    have hfp : ∀ i, Module.FinitePresentation R (F.obj i) := by
      intro i
      letI := hfree i
      letI := hfinite i
      exact Module.finitePresentation_of_projective R (F.obj i)
    have hfactor :=
      finite_free_dual_isMittagLeffler_gives_factorization F hfree hfinite hdualML
    have hallN : ∀ N : ModuleCat R, (colimitPresentationHomInverseSystem F N).IsMittagLeffler :=
      ((directed_colimit_presentation_mittag_leffler_tfae F hfp c).out 2 3).mp hfactor
    exact ⟨⟨{
      index := I
      indexPreorder := inferInstance
      indexNonempty := inferInstance
      indexDirected := inferInstance
      diagram := F
      presentation_isMittagLeffler := ⟨hfp, hallN⟩
      colimitIso := ⟨c⟩
    }⟩⟩
  · letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    letI : Subsingleton M := Module.subsingleton R M
    letI : Module.Free R M := Module.Free.of_subsingleton R M
    letI : Module.Finite R M := ⟨∅, by
      ext x
      simp [Subsingleton.elim x 0]⟩
    letI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
    infer_instance

end

end Module

/-! ### Lemma_10_88_9 (from Chap10) -/
open scoped TensorProduct

universe u v w

namespace Module

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/- Source/core/bridge triage:
* source-facing: the tensor-product stability statement from Lemma `10.88.9`.
* core/canonical: the chapter owner `Module.MittagLeffler` from `Definition_10_88_7`.
* bridge/view: none; the theorem is a derived closure property of the owner abstraction.
-/
-- Proof sketch: choose directed colimit presentations of `M` and `N` by finitely presented
-- modules with eventual factorization of transition maps, as in Proposition `10.88.6`. The
-- tensor-product presentation indexed by pairs `(i, j)` has finitely presented stages by Lemma
-- `10.12.14`, and the tensor products of the eventual factorization maps give the same eventual
-- factorization property for the tensor-product system. Therefore `M ⊗[R] N` is Mittag-Leffler.
/-- Lemma 10.88.9: if `M` and `N` are Mittag-Leffler modules over `R`, then `M ⊗[R] N` is a
Mittag-Leffler `R`-module. -/
theorem mittagLeffler_tensorProduct_of_mittagLeffler
    (hM : MittagLeffler R M) (hN : MittagLeffler R N) :
    MittagLeffler R (M ⊗[R] N) := sorry

end

end Module

/-! ### Lemma_10_88_10 (from Chap10) -/
universe u v w

namespace Module

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain-style sampling:
* primary domain: Mittag-Leffler modules over a commutative ring, organized around the finitely
  presented tensor-kernel criterion from Proposition `10.88.6`.
* inspected owner declarations:
  `directed_colimit_presentation_mittag_leffler_tfae` from `Proposition_10_88_6`,
  `Module.FinitePresentation.equiv_quotient`, and
  `Module.finitePresentation_of_projective`.
* best owner abstraction: the finitely presented tensor-kernel criterion, with finitely presented
  modules as the canonical auxiliary presentation objects.
* layer: `source-facing`; this lemma is the finite-free-source bridge to that criterion.
* primitive data: the module `M`, a finite free source module `F`, and a map `f : F →ₗ[R] M`.
* derived API: the finitely presented comparison module `Q` and the tensor-kernel comparison map
  produced from the criterion.
-/
-- Proof sketch: one direction specializes the finitely presented criterion from Proposition
-- `10.88.6` to finite free source modules. For the converse, given a map from a finitely presented
-- module, use the canonical finite free presentation of that source from
-- `Module.FinitePresentation.equiv_quotient`, apply the assumed finite-free condition on the
-- presenting free module, and descend the resulting comparison map through the quotient to recover
-- the finitely presented criterion.
/-- Lemma 10.88.10: an `R`-module `M` is Mittag-Leffler if and only if every map from a finite
free `R`-module to `M` has the same tensor kernels as some map to a finitely presented
`R`-module. -/
theorem mittagLeffler_iff_finiteFree_maps_share_tensor_kernels_with_finitelyPresented_maps :
    (∀ (P : ModuleCat.{max v w} R) [Module.FinitePresentation R P] (f : P →ₗ[R] M),
        ∃ (Q : ModuleCat.{max v w} R) (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q),
          ∀ N : ModuleCat.{max v w} R,
            LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) ↔
      ∀ (F : ModuleCat.{max v w} R) [Module.Free R F] [Module.Finite R F] (f : F →ₗ[R] M),
        ∃ (Q : ModuleCat.{max v w} R) (_ : Module.FinitePresentation R Q) (g : F →ₗ[R] Q),
          ∀ N : ModuleCat.{max v w} R,
            LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := sorry

end

end Module

/-! ### Lemma_10_88_11 (from Chap10) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace Module

section RestrictScalars

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite R S] [Algebra.FinitePresentation R S]

/- Source/core/bridge triage:
* source-facing: the restriction-of-scalars stability statement from Lemma `10.88.11`.
* core/canonical: the chapter owner `Module.MittagLeffler` from `Definition_10_88_7`.
* bridge/view: viewing an `S`-module as an `R`-module along `R → S`.
-/
-- Proof sketch: choose a directed colimit presentation of `M` by finitely presented `S`-modules
-- with the eventual factorization property from `Module.MittagLeffler S M`. By Lemma `10.36.23`,
-- each stage is also finitely presented over `R`, and the same transition maps and factorization
-- identities remain valid after restriction of scalars, yielding a Mittag-Leffler presentation
-- over `R`.
omit [Module.Finite R S] [Algebra.FinitePresentation R S] in
/-- Helper for Lemma 10.88.11: restricting scalars on `ModuleCat.of S M` gives the expected
`ModuleCat.of R M`. -/
private noncomputable def restrictScalars_obj_iso :
    (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S M) ≅ ModuleCat.of R M :=
  (show ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S M)) ≃ₗ[R] M from
      { __ := AddEquiv.refl _
        map_smul' := fun _ _ ↦ by simp }).toModuleIso

omit [Module.Finite R S] [Algebra.FinitePresentation R S] in
/-- Helper for Lemma 10.88.11: the textbook eventual-factorization condition is preserved when the
same directed system is viewed by restriction of scalars. -/
private lemma eventual_factorization_restrictScalars
    {I : Type w} [Preorder I]
    (F : I ⥤ ModuleCat S)
    (hfactor :
      ∀ i : I, ∃ (j : I) (hij : i ≤ j),
        ∀ (k : I) (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj j,
          F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h) :
    ∀ i : I, ∃ (j : I) (hij : i ≤ j),
      ∀ (k : I) (hik : i ≤ k), ∃ h :
          (F ⋙ ModuleCat.restrictScalars (algebraMap R S)).obj k ⟶
            (F ⋙ ModuleCat.restrictScalars (algebraMap R S)).obj j,
        (F ⋙ ModuleCat.restrictScalars (algebraMap R S)).map (homOfLE hij) =
          (F ⋙ ModuleCat.restrictScalars (algebraMap R S)).map (homOfLE hik) ≫ h := by
  intro i
  obtain ⟨j, hij, hj⟩ := hfactor i
  refine ⟨j, hij, ?_⟩
  intro k hik
  obtain ⟨h, hh⟩ := hj k hik
  refine ⟨(ModuleCat.restrictScalars (algebraMap R S)).map h, ?_⟩
  -- Apply the restriction-of-scalars functor to the source factorization equality.
  simpa using congrArg (fun f ↦ (ModuleCat.restrictScalars (algebraMap R S)).map f) hh

/-- Helper for Lemma 10.88.11: a Mittag-Leffler directed system of `S`-modules stays
Mittag-Leffler after restriction of scalars along a finite, finitely presented map `R → S`. -/
private lemma isMittagLefflerDirectedSystem_restrictScalars
    {I : Type w} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ ModuleCat S)
    (c : colimit F ≅ ModuleCat.of S M)
    (hML : IsMittagLefflerDirectedSystem F) :
    IsMittagLefflerDirectedSystem (F ⋙ ModuleCat.restrictScalars (algebraMap R S)) := by
  let G := ModuleCat.restrictScalars (algebraMap R S)
  let cR :
      colimit (F ⋙ G) ≅ ModuleCat.of R M :=
    (preservesColimitIso G F).symm ≪≫ G.mapIso c ≪≫ restrictScalars_obj_iso (R := R) (S := S)
  rcases hML with ⟨hfpS, hallS⟩
  have hfactorS :
      ∀ i : I, ∃ (j : I) (hij : i ≤ j),
        ∀ (k : I) (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj j,
          F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h :=
    ((directed_colimit_presentation_mittag_leffler_tfae F hfpS c).out 3 2).mp hallS
  have hfactorR :
      ∀ i : I, ∃ (j : I) (hij : i ≤ j),
        ∀ (k : I) (hik : i ≤ k), ∃ h :
            (F ⋙ G).obj k ⟶ (F ⋙ G).obj j,
          (F ⋙ G).map (homOfLE hij) = (F ⋙ G).map (homOfLE hik) ≫ h :=
    eventual_factorization_restrictScalars (R := R) (S := S) F hfactorS
  have hfpR : ∀ i, Module.FinitePresentation R ((F ⋙ G).obj i) := by
    intro i
    -- Lemma `10.36.23` transfers finite presentation of each stage from `S` to `R`.
    let _ : Module R (F.obj i) := Module.compHom (F.obj i) (algebraMap R S)
    let _ : IsScalarTower R S (F.obj i) := IsScalarTower.restrictScalars R S (F.obj i)
    simpa using
      (Module.FinitePresentation.iff_of_finite_finitePresentation
        (R := R) (S := S) (M := F.obj i)).2 (hfpS i)
  have hallR :
      ∀ N : ModuleCat R, (colimitPresentationHomInverseSystem (F ⋙ G) N).IsMittagLeffler :=
    ((directed_colimit_presentation_mittag_leffler_tfae (F ⋙ G) hfpR cR).out 2 3).mp hfactorR
  exact ⟨hfpR, hallR⟩

/-- Lemma 10.88.11: if `R → S` is finite and finitely presented, then every Mittag-Leffler
`S`-module is Mittag-Leffler when viewed as an `R`-module by restriction of scalars. -/
theorem mittagLeffler_restrictScalars_of_finite_finitePresentation [MittagLeffler S M] :
    MittagLeffler R M := by
  classical
  let P : MittagLefflerPresentation S M := Classical.choice (MittagLeffler.exists_presentation
    (R := S) (M := M))
  letI : Preorder P.index := P.indexPreorder
  letI : Nonempty P.index := P.indexNonempty
  letI : IsDirectedOrder P.index := P.indexDirected
  let G := ModuleCat.restrictScalars (algebraMap R S)
  let cS : colimit P.diagram ≅ ModuleCat.of S M := Classical.choice P.colimitIso
  let cR :
      colimit (P.diagram ⋙ G) ≅ ModuleCat.of R M :=
    (preservesColimitIso G P.diagram).symm ≪≫ G.mapIso cS ≪≫
      restrictScalars_obj_iso (R := R) (S := S)
  have hMLR : IsMittagLefflerDirectedSystem (P.diagram ⋙ G) :=
    isMittagLefflerDirectedSystem_restrictScalars
      (R := R) (S := S) (M := M) P.diagram cS P.presentation_isMittagLeffler
  -- Reuse the same index category and diagram after forgetting `S`-linearity.
  exact ⟨⟨{
    index := P.index
    indexPreorder := P.indexPreorder
    indexNonempty := P.indexNonempty
    indexDirected := P.indexDirected
    diagram := P.diagram ⋙ G
    presentation_isMittagLeffler := hMLR
    colimitIso := ⟨cR⟩
  }⟩⟩

end RestrictScalars

end Module

/-! ### Lemma_10_88_12 (from Chap10) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace Module

section

variable {R : Type u} [CommRing R]
variable {M : Type (max u v)} [AddCommGroup M]

/- Source/core/bridge triage:
* source-facing: the quotient-ring comparison statement from Lemma `10.88.12`.
* core/canonical: the chapter owner `Module.MittagLeffler` from `Definition_10_88_7`.
* bridge/view: choose a directed presentation of the quotient module, restrict that same diagram to
  `R`, and use quotient surjectivity to identify the Hom systems over `R` and over `R ⧸ I`.
-/
-- Proof sketch: one direction is Lemma `10.88.11` applied to the quotient map `R → R ⧸ I`. For
-- the converse, choose a directed colimit presentation of `M` by finitely presented `R ⧸ I`-modules;
-- since `I` is finitely generated, the quotient algebra `R ⧸ I` is finite and finitely presented
-- over `R`, so the same stages are finitely presented over `R`, and the Hom inverse systems over
-- `R` and `R ⧸ I` agree because the quotient map is surjective.
/-- Helper for Lemma 10.88.12: restricting scalars on a compatible quotient module does not change
the underlying `R`-module. -/
private noncomputable def restrictScalars_obj_iso
    {S : Type w} [CommRing S] [Algebra R S]
    [Module S M] [Module R M] [IsScalarTower R S M] :
    (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S M) ≅ ModuleCat.of R M :=
  (show ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S M)) ≃ₗ[R] M from
    { __ := AddEquiv.refl M
      map_smul' := fun _ _ ↦ by simp [ModuleCat.restrictScalars.smul_def] }).toModuleIso

/-- Helper for Lemma 10.88.12: an `R`-linear map between quotient modules already commutes with
the quotient scalar action because every quotient scalar lifts to `R`. -/
private lemma quotient_restrictScalars_map_smul
    (I : Ideal R) {X Y : ModuleCat.{max u v} (R ⧸ I)}
    (φ : ((ModuleCat.restrictScalars (algebraMap R (R ⧸ I))).obj X) ⟶
      ((ModuleCat.restrictScalars (algebraMap R (R ⧸ I))).obj Y))
    (s : R ⧸ I) (x : X) :
    φ (s • x) = s • φ x := by
  -- Rewrite the quotient scalar through a preimage in `R` and apply `R`-linearity.
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
  simpa [ModuleCat.restrictScalars.smul_def] using φ.hom.map_smul r x

/-- Helper for Lemma 10.88.12: on quotient modules, an `R`-linear map is automatically
`R ⧸ I`-linear because every quotient scalar lifts along `R → R ⧸ I`. -/
private noncomputable def quotient_linearMap_equiv
    (I : Ideal R) {X Y : Type (max u v)} [AddCommGroup X] [AddCommGroup Y]
    [Module (R ⧸ I) X] [Module (R ⧸ I) Y] [Module R X] [Module R Y]
    [IsScalarTower R (R ⧸ I) X] [IsScalarTower R (R ⧸ I) Y] :
    (X →ₗ[R] Y) ≃ (X →ₗ[R ⧸ I] Y) where
  toFun φ :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := by
        intro s x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
        simpa only [RingHom.id_apply, ← Ideal.Quotient.algebraMap_eq,
          IsScalarTower.algebraMap_smul] using
          φ.map_smul r x }
  invFun φ := φ.restrictScalars R
  left_inv φ := by
    ext x
    rfl
  right_inv φ := by
    ext x
    rfl

/-- Helper for Lemma 10.88.12: every quotient module admits a filtered colimit presentation by
finitely presented quotient modules in the universe used by the target module. -/
private lemma quotient_filtered_presentation_fixed_universe
    (I : Ideal R) [Module (R ⧸ I) M] :
    ∃ (J : Type (max u v)) (_ : SmallCategory J) (_ : IsFiltered J)
      (pres : ColimitPresentation J (ModuleCat.of.{max u v} (R ⧸ I) M)),
        ∀ j, Module.FinitePresentation (R ⧸ I) (pres.diag.obj j) := by
  -- Reuse the earlier owner theorem and unpack its filtered colimit presentation witness
  -- directly in the universe of the target quotient module.
  let QM : ModuleCat.{max u v} (R ⧸ I) := ModuleCat.of.{max u v} (R ⧸ I) M
  simpa [CategoryTheory.ObjectProperty.ind] using
    (show CategoryTheory.ObjectProperty.ind.{max u v}
        (fun N : ModuleCat.{max u v} (R ⧸ I) ↦ Module.FinitePresentation (R ⧸ I) N)
        QM from
      (module_is_isomorphic_to_colimit_of_directed_system_of_finitelyPresented.{u, max u v}
        (R := R ⧸ I) (M := QM)))

/-- Helper for Lemma 10.88.12: restricting scalars along the quotient map does not change the
underlying function of a module morphism. This is the transport-stable rewrite used before the
source-proof Hom comparison is rebundled into an inverse-system statement. -/
private lemma quotient_restrictScalars_map_apply
    (I : Ideal R) {X Y : ModuleCat.{max u v} (R ⧸ I)}
    (f : X ⟶ Y) (x : X) :
    (ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I))).map f x = f x := by
  rfl

/-- Helper for Lemma 10.88.12: after restricting scalars, precomposing with a stage map still acts
by the same underlying function. This isolates the function-level rewrite needed for the future
`Hom_R = Hom_{R ⧸ I}` naturality comparison. -/
private lemma quotient_restrictScalars_precomp_apply
    (I : Ideal R) {X' X N : ModuleCat.{max u v} (R ⧸ I)} (f : X' ⟶ X)
    (ψ : ((ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I))).obj X) ⟶
      ((ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I))).obj N)) (x : X') :
    (((ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I))).map f) ≫ ψ) x = ψ (f x) := by
  -- Both restriction of scalars and categorical composition keep the same underlying function.
  rfl

/-- Helper for Lemma 10.88.12: reindexing a filtered quotient presentation along a final directed
functor preserves finite presentation of every stage. -/
private lemma quotient_reindexed_stage_finitePresentation
    (I : Ideal R) [Module (R ⧸ I) M]
    {J : Type (max u v)} [SmallCategory J] [IsFiltered J]
    (pres : ColimitPresentation J (ModuleCat.of.{max u v} (R ⧸ I) M))
    (hfp : ∀ j, Module.FinitePresentation (R ⧸ I) (pres.diag.obj j))
    {K : Type (max u v)} [PartialOrder K] [IsDirected K (· ≤ ·)] [Nonempty K]
    (FJ : K ⥤ J) [FJ.Final] :
    ∀ k, Module.FinitePresentation (R ⧸ I) ((pres.reindex FJ).diag.obj k) := by
  -- Reindexing only relabels the same quotient modules, so the stagewise hypothesis is unchanged.
  intro k
  simpa using hfp (FJ.obj k)

/-- Helper for Lemma 10.88.12: for one fixed target quotient module, the `R`-linear and
`R ⧸ I`-linear Hom stages in the chosen presentation are identified by the surjectivity of
`R → R ⧸ I`. -/
private noncomputable def quotient_hom_inverseSystem_stage_equiv
    (I : Ideal R) {K : Type (max u v)} [Preorder K]
    (F : K ⥤ ModuleCat.{max u v} (R ⧸ I))
    (N : ModuleCat.{max u v} (R ⧸ I)) (j : Kᵒᵖ) :
    ((colimitPresentationHomInverseSystem
        (F ⋙ ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I)))
        ((ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I))).obj N)).obj j) ≃
      ((colimitPresentationHomInverseSystem F N).obj j) :=
  let _ : Module R (F.obj (Opposite.unop j)) :=
    Module.compHom (F.obj (Opposite.unop j)) (algebraMap R (R ⧸ I))
  let _ : Module R N := Module.compHom N (algebraMap R (R ⧸ I))
  let _ : IsScalarTower R (R ⧸ I) (F.obj (Opposite.unop j)) :=
    IsScalarTower.restrictScalars R (R ⧸ I) (F.obj (Opposite.unop j))
  let _ : IsScalarTower R (R ⧸ I) N := IsScalarTower.restrictScalars R (R ⧸ I) N
  { toFun := fun ψ ↦
      ModuleCat.ofHom <|
        (quotient_linearMap_equiv (R := R) (I := I)
          (X := F.obj (Opposite.unop j)) (Y := N)) ψ.hom
    invFun := fun ψ ↦
      ModuleCat.ofHom <|
        ((quotient_linearMap_equiv (R := R) (I := I)
          (X := F.obj (Opposite.unop j)) (Y := N)).symm ψ.hom)
    left_inv := by
      intro ψ
      apply ModuleCat.hom_ext
      ext x
      rfl
    right_inv := by
      intro ψ
      apply ModuleCat.hom_ext
      ext x
      rfl }

/-- Helper for Lemma 10.88.12: the stagewise quotient-Hom identifications commute with the
transition maps in the inverse systems `Hom_R(Mᵢ, N)` and `Hom_{R ⧸ I}(Mᵢ, N)`. -/
private lemma quotient_hom_inverseSystem_stage_equiv_naturality
    (I : Ideal R) {K : Type (max u v)} [Preorder K]
    (F : K ⥤ ModuleCat.{max u v} (R ⧸ I))
    (N : ModuleCat.{max u v} (R ⧸ I)) {i j : Kᵒᵖ} (g : j ⟶ i)
    (ψ : ((colimitPresentationHomInverseSystem
        (F ⋙ ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I)))
        ((ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I))).obj N)).obj j)) :
    quotient_hom_inverseSystem_stage_equiv (R := R) I F N i
        (((colimitPresentationHomInverseSystem
            (F ⋙ ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I)))
            ((ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I))).obj N)).map g) ψ) =
      ((colimitPresentationHomInverseSystem F N).map g)
        (quotient_hom_inverseSystem_stage_equiv (R := R) I F N j ψ) := by
  -- Both sides are the same precomposition map; only the scalar-linearity packaging differs.
  change ModuleCat.ofHom _ = ModuleCat.ofHom _
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Helper for Lemma 10.88.12: if the fixed-target inverse system of `R`-linear maps is
Mittag-Leffler after restricting scalars, then the equal inverse system of quotient-linear maps is
Mittag-Leffler as well. -/
private lemma quotient_hom_inverseSystem_isMittagLeffler_of_restrictScalars
    (I : Ideal R) {K : Type (max u v)} [Preorder K] [Nonempty K] [IsDirectedOrder K]
    (F : K ⥤ ModuleCat.{max u v} (R ⧸ I))
    (N : ModuleCat.{max u v} (R ⧸ I))
    (hR :
      (colimitPresentationHomInverseSystem
        (F ⋙ ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I)))
        ((ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I))).obj N)).IsMittagLeffler) :
    (colimitPresentationHomInverseSystem F N).IsMittagLeffler := by
  let G := ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I))
  let FR := colimitPresentationHomInverseSystem (F ⋙ G) (G.obj N)
  let FS := colimitPresentationHomInverseSystem F N
  rw [Functor.isMittagLeffler_iff_subset_range_comp] at hR ⊢
  intro j
  obtain ⟨i, f, hf⟩ := hR j
  refine ⟨i, f, ?_⟩
  intro k g y hy
  rcases hy with ⟨x, rfl⟩
  let xR := (quotient_hom_inverseSystem_stage_equiv (R := R) I F N i).symm x
  -- Transport the range witness to the restricted-scalar Hom inverse system.
  have hxR : FR.map f xR ∈ Set.range (FR.map (g ≫ f)) := by
    exact hf g ⟨xR, rfl⟩
  rcases hxR with ⟨zR, hzR⟩
  refine ⟨quotient_hom_inverseSystem_stage_equiv (R := R) I F N k zR, ?_⟩
  -- Apply the stagewise identifications at the source and target stages.
  calc
    FS.map (g ≫ f) (quotient_hom_inverseSystem_stage_equiv (R := R) I F N k zR)
        = quotient_hom_inverseSystem_stage_equiv (R := R) I F N j (FR.map (g ≫ f) zR) := by
            symm
            exact quotient_hom_inverseSystem_stage_equiv_naturality
              (R := R) I F N (g ≫ f) zR
    _ = quotient_hom_inverseSystem_stage_equiv (R := R) I F N j (FR.map f xR) := by
          rw [hzR]
    _ = FS.map f (quotient_hom_inverseSystem_stage_equiv (R := R) I F N i xR) := by
          exact quotient_hom_inverseSystem_stage_equiv_naturality (R := R) I F N f xR
    _ = FS.map f x := by
          rw [Equiv.apply_symm_apply]

/-- Lemma 10.88.12: if `S = R ⧸ I` for a finitely generated ideal `I`, then an `S`-module `M` is
Mittag-Leffler over `R` if and only if it is Mittag-Leffler over `S`. -/
theorem mittagLeffler_iff_over_ring_and_quotient (I : Ideal R) (hI : I.FG)
    [Module (R ⧸ I) M] [Module R M] [IsScalarTower R (R ⧸ I) M] :
    MittagLeffler.{u, max u v} R M ↔ MittagLeffler.{u, max u v} (R ⧸ I) M := by
  constructor
  · intro hM
    letI : Algebra.FinitePresentation R (R ⧸ I) := Algebra.FinitePresentation.quotient hI
    letI : Module.Finite R (R ⧸ I) := by infer_instance
    classical
    -- Route correction: keep the source-faithful quotient presentation, but transfer the final
    -- Hom inverse systems targetwise instead of rebundling factorization maps.
    obtain ⟨J, _, _, pres, hfpFilt⟩ :=
      quotient_filtered_presentation_fixed_universe (R := R) (M := M) I
    obtain ⟨K, _, _, _, FJ, _⟩ := CategoryTheory.IsFiltered.exists_directed J
    let P : ColimitPresentation K (ModuleCat.of.{max u v} (R ⧸ I) M) := pres.reindex FJ
    let F : K ⥤ ModuleCat.{max u v} (R ⧸ I) := P.diag
    let cS : colimit F ≅ ModuleCat.of.{max u v} (R ⧸ I) M :=
      (P.isColimit.coconePointUniqueUpToIso (colimit.isColimit F)).symm
    have hfpS : ∀ k, Module.FinitePresentation (R ⧸ I) (F.obj k) := by
      -- Reindexing only changes the directed index set, not the quotient-module stages.
      intro k
      exact quotient_reindexed_stage_finitePresentation (R := R) (M := M) I pres hfpFilt FJ k
    let G := ModuleCat.restrictScalars.{max u v} (algebraMap R (R ⧸ I))
    let cR : colimit (F ⋙ G) ≅ ModuleCat.of.{max u v} R M :=
      (preservesColimitIso G F).symm ≪≫ G.mapIso cS ≪≫
        restrictScalars_obj_iso (R := R) (S := R ⧸ I)
    have hfpR : ∀ k, Module.FinitePresentation R ((F ⋙ G).obj k) := by
      -- Lemma `10.36.23` upgrades each finitely presented quotient stage to a finitely presented
      -- `R`-module stage because `R ⧸ I` is finite and finitely presented over `R`.
      intro k
      let _ : Module R (F.obj k) := Module.compHom (F.obj k) (algebraMap R (R ⧸ I))
      let _ : IsScalarTower R (R ⧸ I) (F.obj k) :=
        IsScalarTower.restrictScalars R (R ⧸ I) (F.obj k)
      simpa [F, G] using
        (Module.FinitePresentation.iff_of_finite_finitePresentation
          (R := R) (S := R ⧸ I) (M := F.obj k)).2 (hfpS k)
    letI : MittagLeffler.{u, max u v} R M := hM
    let PR : MittagLefflerPresentation R M := Classical.choice (MittagLeffler.exists_presentation
      (R := R) (M := M))
    letI : Preorder PR.index := PR.indexPreorder
    letI : Nonempty PR.index := PR.indexNonempty
    letI : IsDirectedOrder PR.index := PR.indexDirected
    let cPR : colimit PR.diagram ≅ ModuleCat.of.{max u v} R M := Classical.choice PR.colimitIso
    have hdom :
        ∀ (Q : ModuleCat.{max u v} R) [Module.FinitePresentation R Q] (f : Q →ₗ[R] M),
          ∃ (Q' : ModuleCat.{max u v} R) (_ : Module.FinitePresentation R Q') (g : Q →ₗ[R] Q'),
            ∀ N : ModuleCat.{max u v} R,
              LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
      rcases PR.presentation_isMittagLeffler with ⟨hfpPR, hallPR⟩
      -- Clause `(1)` in Proposition `10.88.6` depends only on `M`, not on the chosen presentation.
      exact ((directed_colimit_presentation_mittag_leffler_tfae PR.diagram hfpPR cPR).out 3 0).mp
        hallPR
    have hallR :
        ∀ N : ModuleCat.{max u v} R, (colimitPresentationHomInverseSystem (F ⋙ G) N).IsMittagLeffler :=
      ((directed_colimit_presentation_mittag_leffler_tfae (F ⋙ G) hfpR cR).out 0 3).mp hdom
    have hallS :
        ∀ N : ModuleCat.{max u v} (R ⧸ I), (colimitPresentationHomInverseSystem F N).IsMittagLeffler := by
      -- For each target quotient module, the textbook equality
      -- `Hom_R(Mᵢ, N) = Hom_{R ⧸ I}(Mᵢ, N)` transfers the Mittag-Leffler condition.
      intro N
      exact quotient_hom_inverseSystem_isMittagLeffler_of_restrictScalars
        (R := R) I F N (hallR (G.obj N))
    -- Package the chosen directed quotient presentation as a Mittag-Leffler presentation over
    -- `R ⧸ I`.
    exact ⟨⟨{
      index := K
      indexPreorder := inferInstance
      indexNonempty := inferInstance
      indexDirected := inferInstance
      diagram := F
      presentation_isMittagLeffler := ⟨hfpS, hallS⟩
      colimitIso := ⟨cS⟩
    }⟩⟩
  · intro hM
    letI : Algebra.FinitePresentation R (R ⧸ I) := Algebra.FinitePresentation.quotient hI
    letI : Module.Finite R (R ⧸ I) := by infer_instance
    letI : MittagLeffler.{u, max u v} (R ⧸ I) M := hM
    -- The reverse implication is exactly the finite, finitely presented restriction-of-scalars
    -- bridge from Lemma `10.88.11`.
    simpa using
      (mittagLeffler_restrictScalars_of_finite_finitePresentation
        (R := R) (S := R ⧸ I) (M := M))

end

end Module

/-! ### Remark_10_88_13 (from Chap10) -/
universe u v

namespace Module

section

variable {R : Type u} [CommRing R]

local instance (M : ModuleCat.{v} (DualNumber R)) : Module R M :=
  Module.compHom M (algebraMap R (DualNumber R))

/- Source/core/bridge triage:
* source-facing: existence of a dual-number counterexample to ascent for the Mittag-Leffler
  property.
* core/canonical: the chapter owner `Module.MittagLeffler` on the underlying module carrier of a
  bundled `ModuleCat`.
* bridge/view: the induced `R`-module structure on a `DualNumber R`-module via restriction of
  scalars along `algebraMap R (DualNumber R)`.
-/
-- Proof sketch: start from a non-Mittag-Leffler `R`-module `M₀` and choose a presentation by free
-- modules `F₁ ⟶ F₀ ⟶ M₀ ⟶ 0`. Endow `F₁ ⊕ F₀` with the dual-number action coming from the square-zero
-- endomorphism given by the presentation map. As an `R`-module this object is free, hence
-- Mittag-Leffler over `R`; if it were Mittag-Leffler over `DualNumber R`, then reduction modulo
-- `ε` would also be Mittag-Leffler, forcing `F₁ ⊕ M₀` to be Mittag-Leffler over `R`, a
-- contradiction.
/-- Remark 10.88.13: assuming there exists an `R`-module which is not Mittag-Leffler, the dual
numbers over `R` provide a counterexample to ascent of the Mittag-Leffler property: there exists a
`DualNumber R`-module which is Mittag-Leffler when viewed as an `R`-module, but which is not
Mittag-Leffler as a `DualNumber R`-module. -/
theorem exists_dualNumber_module_mittagLeffler_over_base_not_over_dualNumber
    (h₀ : ∃ M₀ : ModuleCat.{v} R, ¬ MittagLeffler R M₀) :
    ∃ M : ModuleCat.{v} (DualNumber R),
      MittagLeffler R M ∧ ¬ MittagLeffler (DualNumber R) M := sorry

end

end Module
