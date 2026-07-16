import stacks_proof.stacks_project.Chap10.Proposition_10_58_7.GrothendieckClasses

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open CategoryTheory
open CategoryTheory.ShortComplex.ShortExact
open HomogeneousIdeal

section

/-- Helper for Chap10 Proposition 10 58 7: the integer grading carries the natural degree-shift
action by `ℕ`. -/
local instance instAddActionNatIntHomogeneousQuotientPieces10587 : AddAction ℕ ℤ where
  vadd n d := (n : ℤ) + d
  zero_vadd := by
    intro d
    change ((0 : ℕ) : ℤ) + d = d
    simp
  add_vadd := by
    intro m n d
    change (((m + n : ℕ) : ℤ) + d) = (m : ℤ) + ((n : ℤ) + d)
    simp [Nat.cast_add, add_assoc]

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜]
variable [IsNoetherianRing S]

/-- Helper for Proposition 10.58.7: in homogeneous quotient-piece arguments, an `S`-module is
viewed as an `S₀`-module by restriction of scalars along `𝒜 0 → S`. -/
local instance graded_zero_piece_module_homogeneousQuotientPieces10587
    {M : Type w} [AddCommGroup M] [Module S M] : Module (𝒜 0) M :=
  Module.restrictScalars (𝒜 0) S M

/-- Helper for Proposition 10.58.7: each graded piece of a quotient graded module receives the
corresponding homogeneous component of the source module via the quotient map. -/
def homogeneous_quotient_module_component_map
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ]
    (N : Submodule S M) (d : ℤ) :
    ℳ d →ₗ[S] quotient_grading ℳ N d :=
  LinearMap.codRestrict
    (quotient_grading ℳ N d)
    (N.mkQ.domRestrict (ℳ d))
    (fun x ↦ ⟨x, x.2, rfl⟩)

/-- Helper for Proposition 10.58.7: quotienting a graded module by a homogeneous submodule
preserves the graded action of the original graded ring. -/
instance homogeneous_quotient_module_setLikeGradedSMul
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    (N : Submodule S M) :
    SetLike.GradedSMul 𝒜 (quotient_grading ℳ N) where
  smul_mem := by
    intro i j a x ha hx
    rcases hx with ⟨y, hy, rfl⟩
    refine ⟨a • y, SetLike.GradedSMul.smul_mem ha hy, ?_⟩
    -- The quotient action is defined on representatives, so the witness is `a • y`.
    simpa using (Submodule.Quotient.mk_smul N a y).symm

/-- Helper for Proposition 10.58.7: the quotient graded module `M / (a)M` inherits the graded
action of the quotient graded ring `S / (a)`. -/
lemma degree_one_singleton_quotient_module_setLikeGradedSMul_over_quotient
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {a : S} :
    SetLike.GradedSMul
      (fun n ↦
        (𝒜 n).map
          ((Ideal.Quotient.mkₐ R (Ideal.span ({a} : Set S))).toLinearMap))
      (fun d ↦ quotient_grading ℳ ((Ideal.span ({a} : Set S)) • (⊤ : Submodule S M)) d) where
  smul_mem := by
    intro i j xbar ybar hx hy
    rcases hx with ⟨x, hx, rfl⟩
    rcases hy with ⟨y, hy, rfl⟩
    refine ⟨x • y, SetLike.GradedSMul.smul_mem hx hy, ?_⟩
    -- The quotient-side grading is still represented by the source homogeneous witnesses.
    simpa using
      (Module.Quotient.mk_smul_mk
        (I := Ideal.span ({a} : Set S)) (r := x) (m := y)).symm

/-- Helper for Proposition 10.58.7: before descending to the quotient by a homogeneous
submodule, decompose an element into its homogeneous summands and map each summand to the
quotient componentwise. -/
noncomputable def homogeneous_quotient_module_predecompose
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ]
    (N : Submodule S M) :
    M →ₗ[S] DirectSum ℤ (fun d ↦ quotient_grading ℳ N d) :=
  (DirectSum.lmap fun d ↦ homogeneous_quotient_module_component_map (ℳ := ℳ) N d).comp
    (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

/-- Helper for Proposition 10.58.7: on a homogeneous element of degree `d`, the quotient
predecomposition is concentrated in the direct-sum slot of degree `d`. -/
lemma homogeneous_quotient_module_predecompose_eq_lof_of_mem
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ]
    (N : Submodule S M)
    {x : M} {d : ℤ} (hx : x ∈ ℳ d) :
    homogeneous_quotient_module_predecompose (ℳ := ℳ) N x =
      DirectSum.lof S ℤ (fun e ↦ quotient_grading ℳ N e) d
        (homogeneous_quotient_module_component_map (ℳ := ℳ) N d ⟨x, hx⟩) := by
  apply DFinsupp.ext
  intro e
  by_cases hde : d = e
  · subst hde
    -- In the matching degree, the source decomposition already consists of the given summand.
    have hsame : (DirectSum.decompose ℳ x d : ℳ d) = ⟨x, hx⟩ := by
      apply Subtype.ext
      simpa using (DirectSum.decompose_of_mem_same ℳ hx)
    rw [homogeneous_quotient_module_predecompose, LinearMap.comp_apply, DirectSum.lmap_apply]
    simpa [DirectSum.decomposeLinearEquiv_apply, DirectSum.lof_eq_of, hsame] using
      congrArg (homogeneous_quotient_module_component_map (ℳ := ℳ) N d) hsame
  · have hed : e ≠ d := by
      intro hed
      exact hde hed.symm
    have hdecomp : (((DirectSum.decompose ℳ) x) e : M) = 0 := by
      simpa using (DirectSum.decompose_of_mem_ne ℳ hx hde)
    -- Off the matching degree, the source homogeneous projection already vanishes.
    have hzero : ((DirectSum.decompose ℳ x e : ℳ e)) = 0 := by
      apply Subtype.ext
      simpa using hdecomp
    rw [homogeneous_quotient_module_predecompose, LinearMap.comp_apply, DirectSum.lmap_apply]
    have hcoord :
        ((DirectSum.decomposeLinearEquiv ℳ x) e) = ((DirectSum.decompose ℳ) x e) := rfl
    have hleft :
        (homogeneous_quotient_module_component_map (ℳ := ℳ) N e)
            ((DirectSum.decompose ℳ) x e) = 0 := by
      simpa [homogeneous_quotient_module_component_map,
        hzero]
    calc
      (homogeneous_quotient_module_component_map (ℳ := ℳ) N e)
          ((DirectSum.decomposeLinearEquiv ℳ x) e) =
          (homogeneous_quotient_module_component_map (ℳ := ℳ) N e)
            ((DirectSum.decompose ℳ) x e) := by
              simpa [DirectSum.decomposeLinearEquiv_apply] using
                congrArg (homogeneous_quotient_module_component_map (ℳ := ℳ) N e) hcoord
      _ = 0 := hleft
      _ =
          ((DirectSum.lof S ℤ (fun e ↦ quotient_grading ℳ N e) d)
            ((homogeneous_quotient_module_component_map (ℳ := ℳ) N d) ⟨x, hx⟩)) e := by
              symm
              exact DirectSum.of_eq_of_ne _ _ _ hed

/-- Helper for Proposition 10.58.7: if `N` is homogeneous, then the componentwise quotient
predecomposition annihilates every element of `N`. -/
lemma homogeneous_quotient_module_predecompose_eq_zero_of_mem
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ]
    {N : Submodule S M}
    (hN : N.IsHomogeneous ℳ)
    {x : M} (hx : x ∈ N) :
    homogeneous_quotient_module_predecompose (ℳ := ℳ) N x = 0 := by
  apply DFinsupp.ext
  intro d
  have hproj_mem : (((DirectSum.decompose ℳ x d : ℳ d) : M)) ∈ N := hN d hx
  have hproj_zero :
      N.mkQ (((DirectSum.decompose ℳ x d : ℳ d) : M)) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero N).2 hproj_mem
  -- Each projected summand already lies in `N`, so it dies after quotienting.
  rw [homogeneous_quotient_module_predecompose, LinearMap.comp_apply, DirectSum.lmap_apply]
  apply Subtype.ext
  simpa [homogeneous_quotient_module_component_map, DirectSum.decomposeLinearEquiv_apply] using
    hproj_zero

/-- Helper for Proposition 10.58.7: a homogeneous submodule lies in the kernel of the
componentwise quotient predecomposition, so the latter descends to the quotient module. -/
lemma homogeneous_quotient_module_predecompose_le_ker
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ]
    {N : Submodule S M}
    (hN : N.IsHomogeneous ℳ) :
    N ≤ LinearMap.ker (homogeneous_quotient_module_predecompose (ℳ := ℳ) N) := by
  intro x hx
  -- The vanishing statement on `N` is exactly the kernel condition needed for `liftQ`.
  exact homogeneous_quotient_module_predecompose_eq_zero_of_mem (ℳ := ℳ) hN hx

/-- Helper for Proposition 10.58.7: the componentwise quotient predecomposition descends to a
linear decomposition map on the quotient by a homogeneous submodule. -/
noncomputable def homogeneous_quotient_module_decomposeLinear
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ]
    {N : Submodule S M}
    (hN : N.IsHomogeneous ℳ) :
    M ⧸ N →ₗ[S] DirectSum ℤ (fun d ↦ quotient_grading ℳ N d) :=
  Submodule.liftQ N
    (homogeneous_quotient_module_predecompose (ℳ := ℳ) N)
    (homogeneous_quotient_module_predecompose_le_ker (ℳ := ℳ) hN)

/-- Helper for Proposition 10.58.7: recomposing the descended quotient-module decomposition
recovers the quotient class. -/
lemma homogeneous_quotient_module_decomposeLinear_left_inv
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ]
    {N : Submodule S M}
    (hN : N.IsHomogeneous ℳ) :
    DirectSum.coeLinearMap (fun d ↦ quotient_grading ℳ N d) ∘ₗ
        homogeneous_quotient_module_decomposeLinear (ℳ := ℳ) hN =
      LinearMap.id := by
  let ℳbar : ℤ → Submodule S (M ⧸ N) := fun d ↦ quotient_grading ℳ N d
  let predecomposeBar :
      M →ₗ[S] DirectSum ℤ (fun d ↦ ℳbar d) :=
    homogeneous_quotient_module_predecompose (ℳ := ℳ) N
  have hsource :
      DirectSum.coeLinearMap ℳbar ∘ₗ predecomposeBar = N.mkQ := by
    -- Compare both maps on each homogeneous summand of the source module.
    apply DirectSum.decompose_lhom_ext (ℳ := ℳ)
    intro d
    apply LinearMap.ext
    intro x
    change DirectSum.coeLinearMap ℳbar
        (homogeneous_quotient_module_predecompose (ℳ := ℳ) N (x : M)) =
      N.mkQ x
    rw [homogeneous_quotient_module_predecompose_eq_lof_of_mem (ℳ := ℳ) N x.2]
    rw [DirectSum.coeLinearMap_lof]
    rfl
  -- Descend the source equality to the quotient by checking it on representatives.
  apply Submodule.linearMap_qext (p := N)
  calc
    ((DirectSum.coeLinearMap (fun d ↦ quotient_grading ℳ N d) ∘ₗ
          homogeneous_quotient_module_decomposeLinear (ℳ := ℳ) hN) ∘ₗ N.mkQ) =
        DirectSum.coeLinearMap ℳbar ∘ₗ predecomposeBar := by
          ext x
          have hLift :
              homogeneous_quotient_module_decomposeLinear (ℳ := ℳ) hN (N.mkQ x) =
                predecomposeBar x := by
            simpa [predecomposeBar, homogeneous_quotient_module_decomposeLinear] using
              (Submodule.liftQ_apply
                (p := N)
                (f := homogeneous_quotient_module_predecompose (ℳ := ℳ) N)
                (h := homogeneous_quotient_module_predecompose_le_ker (ℳ := ℳ) hN) x)
          simpa [LinearMap.comp_apply] using congrArg (DirectSum.coeLinearMap ℳbar) hLift
    _ = N.mkQ := hsource
    _ = LinearMap.id ∘ₗ N.mkQ := by
          rfl

/-- Helper for Proposition 10.58.7: the descended quotient-module decomposition sends each
homogeneous quotient class back to the matching direct-sum generator. -/
lemma homogeneous_quotient_module_decomposeLinear_right_inv
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ]
    {N : Submodule S M}
    (hN : N.IsHomogeneous ℳ) :
    homogeneous_quotient_module_decomposeLinear (ℳ := ℳ) hN ∘ₗ
        DirectSum.coeLinearMap (fun d ↦ quotient_grading ℳ N d) =
      LinearMap.id := by
  let ℳbar : ℤ → Submodule S (M ⧸ N) := fun d ↦ quotient_grading ℳ N d
  -- A direct-sum map is determined by its values on the homogeneous `lof` generators.
  apply DirectSum.linearMap_ext
  intro d
  apply LinearMap.ext
  intro xbar
  rcases xbar.2 with ⟨x, hx, hqx⟩
  have hxbar :
      xbar = ⟨N.mkQ x, ⟨x, hx, rfl⟩⟩ := by
    apply Subtype.ext
    exact hqx.symm
  have hpre :
      homogeneous_quotient_module_decomposeLinear (ℳ := ℳ) hN (N.mkQ x) =
        DirectSum.lof S ℤ (fun e ↦ ℳbar e) d ⟨N.mkQ x, ⟨x, hx, rfl⟩⟩ := by
    -- A homogeneous representative still yields the expected direct-sum basis vector after
    -- passing to the quotient.
    simpa [ℳbar, homogeneous_quotient_module_decomposeLinear,
      homogeneous_quotient_module_component_map] using
      (homogeneous_quotient_module_predecompose_eq_lof_of_mem (ℳ := ℳ) N hx)
  simpa [LinearMap.comp_apply, hxbar] using hpre

/-- Helper for Proposition 10.58.7: quotienting a graded module by a homogeneous submodule
inherits a direct-sum decomposition on the quotient graded pieces. -/
@[reducible] noncomputable def homogeneous_quotient_module_decomposition
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ]
    {N : Submodule S M}
    (hN : N.IsHomogeneous ℳ) :
    DirectSum.Decomposition (fun d ↦ quotient_grading ℳ N d) :=
  DirectSum.Decomposition.ofLinearMap
    (ℳ := fun d ↦ quotient_grading ℳ N d)
    (homogeneous_quotient_module_decomposeLinear (ℳ := ℳ) hN)
    (homogeneous_quotient_module_decomposeLinear_left_inv (ℳ := ℳ) hN)
    (homogeneous_quotient_module_decomposeLinear_right_inv (ℳ := ℳ) hN)

/-- Helper for Proposition 10.58.7: the degree-`d` piece of a submodule is finite over `S₀`
because `S₀` is Noetherian and the ambient degree piece is finite. -/
lemma homogeneous_submodule_degree_piece_finite
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    [Module.Finite S M] [Algebra.FiniteType (𝒜 0) S]
    (K : Submodule S M) (d : ℤ) :
    Module.Finite (𝒜 0) ((ℳ d).comap K.subtype) := by
  let _ : Module.Finite (𝒜 0) (ℳ d) := finite_degree_component_of_finiteType 𝒜 ℳ d
  let f : ((ℳ d).comap K.subtype) →ₗ[𝒜 0] ℳ d :=
    { toFun := fun x ↦ ⟨x.1, x.2⟩
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro c x
        rfl }
  have hf_injective : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ℳ d ↦ (z : M)) hxy
  -- The degree piece of `K` embeds in the finite ambient degree piece.
  exact Module.Finite.of_injective f hf_injective

/-- Helper for Proposition 10.58.7: the degree-`d` part of a homogeneous submodule, viewed as a
finitely generated `S₀`-module. -/
noncomputable def homogeneous_submodule_degree_piece_fgModuleCat
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    [Module.Finite S M] [Algebra.FiniteType (𝒜 0) S]
    (K : Submodule S M) (d : ℤ) :
    FGModuleCat (𝒜 0) :=
  let _ : Module (𝒜 0) ((ℳ d).comap K.subtype) :=
    Module.restrictScalars (𝒜 0) S ((ℳ d).comap K.subtype)
  let _ : Module.Finite (𝒜 0) ((ℳ d).comap K.subtype) :=
    homogeneous_submodule_degree_piece_finite (𝒜 := 𝒜) (ℳ := ℳ) K d
  FGModuleCat.of (𝒜 0) ((ℳ d).comap K.subtype)

/-- Helper for Proposition 10.58.7: the degree-`d` quotient piece is finite over `S₀` because it
is the image of the finite ambient degree piece under the quotient map. -/
lemma homogeneous_quotient_degree_piece_finite
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    [Module.Finite S M] [Algebra.FiniteType (𝒜 0) S]
    (K : Submodule S M) (d : ℤ) :
    Module.Finite (𝒜 0) (quotient_grading ℳ K d) := by
  let _ : Module.Finite (𝒜 0) (ℳ d) := finite_degree_component_of_finiteType 𝒜 ℳ d
  let f : ℳ d →ₗ[𝒜 0] quotient_grading ℳ K d :=
    { toFun := fun x ↦ ⟨K.mkQ x, ⟨x, x.2, rfl⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro c x
        apply Subtype.ext
        rfl }
  -- The componentwise quotient map is surjective by the definition of `quotient_grading`.
  refine Module.Finite.of_surjective f ?_
  intro xbar
  rcases xbar.2 with ⟨x, hx, hxbar⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  exact Subtype.ext hxbar

/-- Helper for Proposition 10.58.7: the degree-`d` part of the quotient by a homogeneous
submodule, viewed as a finitely generated `S₀`-module. -/
noncomputable def homogeneous_quotient_degree_piece_fgModuleCat
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    [Module.Finite S M] [Algebra.FiniteType (𝒜 0) S]
    (K : Submodule S M) (d : ℤ) :
    FGModuleCat (𝒜 0) :=
  let _ : Module (𝒜 0) (quotient_grading ℳ K d) :=
    Module.restrictScalars (𝒜 0) S (quotient_grading ℳ K d)
  let _ : Module.Finite (𝒜 0) (quotient_grading ℳ K d) :=
    homogeneous_quotient_degree_piece_finite (𝒜 := 𝒜) (ℳ := ℳ) K d
  FGModuleCat.of (𝒜 0) (quotient_grading ℳ K d)

/-- Helper for Proposition 10.58.7: for a homogeneous submodule `K`, the degree-`d` pieces fit
into the short exact sequence `0 → K_d → M_d → (M / K)_d → 0`, hence their classes add in
`K'_0(S₀)`. -/
lemma homogeneous_submodule_degreewise_k0_add
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    [Module.Finite S M] [Algebra.FiniteType (𝒜 0) S]
    {K : Submodule S M}
    (hK : K.IsHomogeneous ℳ)
    (d : ℤ) :
    gradedPieceFiniteGrothendieckGroupClass 𝒜 ℳ d =
      finiteGrothendieckGroupOf (𝒜 0)
        (homogeneous_submodule_degree_piece_fgModuleCat (𝒜 := 𝒜) (ℳ := ℳ) K d) +
      finiteGrothendieckGroupOf (𝒜 0)
        (homogeneous_quotient_degree_piece_fgModuleCat (𝒜 := 𝒜) (ℳ := ℳ) K d) := by
  let _ : Module (𝒜 0) (ℳ d) := Module.restrictScalars (𝒜 0) S (ℳ d)
  let _ : Module.Finite (𝒜 0) (ℳ d) := finite_degree_component_of_finiteType 𝒜 ℳ d
  let _ : Module (𝒜 0) ((ℳ d).comap K.subtype) :=
    Module.restrictScalars (𝒜 0) S ((ℳ d).comap K.subtype)
  let _ : Module.Finite (𝒜 0) ((ℳ d).comap K.subtype) :=
    homogeneous_submodule_degree_piece_finite (𝒜 := 𝒜) (ℳ := ℳ) K d
  let _ : Module (𝒜 0) (quotient_grading ℳ K d) :=
    Module.restrictScalars (𝒜 0) S (quotient_grading ℳ K d)
  let _ : Module.Finite (𝒜 0) (quotient_grading ℳ K d) :=
    homogeneous_quotient_degree_piece_finite (𝒜 := 𝒜) (ℳ := ℳ) K d
  let i : ((ℳ d).comap K.subtype) →ₗ[𝒜 0] ℳ d :=
    { toFun := fun x ↦ ⟨x.1, x.2⟩
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro c x
        rfl }
  let q : ℳ d →ₗ[𝒜 0] quotient_grading ℳ K d :=
    { toFun := fun x ↦ ⟨K.mkQ x, ⟨x, x.2, rfl⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro c x
        apply Subtype.ext
        rfl }
  let T : ShortComplex (FGModuleCat (𝒜 0)) :=
    { X₁ := homogeneous_submodule_degree_piece_fgModuleCat (𝒜 := 𝒜) (ℳ := ℳ) K d
      X₂ := FGModuleCat.of (𝒜 0) (ℳ d)
      X₃ := homogeneous_quotient_degree_piece_fgModuleCat (𝒜 := 𝒜) (ℳ := ℳ) K d
      f := FGModuleCat.ofHom i
      g := FGModuleCat.ofHom q
      zero := by
        ext x
        apply Subtype.ext
        exact (Submodule.Quotient.mk_eq_zero K).2 x.1.2 }
  have hExact : Function.Exact i q := by
    intro x
    constructor
    · intro hx
      have hx' : (q x : M ⧸ K) = 0 := congrArg (fun z : quotient_grading ℳ K d ↦ (z : M ⧸ K)) hx
      have hxK : (x : M) ∈ K := by
        simpa [q] using (Submodule.Quotient.mk_eq_zero K).1 hx'
      refine ⟨⟨⟨x, hxK⟩, x.2⟩, ?_⟩
      apply Subtype.ext
      rfl
    · rintro ⟨x, rfl⟩
      apply Subtype.ext
      exact (Submodule.Quotient.mk_eq_zero K).2 x.1.2
  have hi_injective : Function.Injective i := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ℳ d ↦ (z : M)) hxy
  have hq_surjective : Function.Surjective q := by
    intro xbar
    rcases xbar.2 with ⟨x, hx, hxbar⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxbar
  have hT : (T.map (ModuleCat.isFG (𝒜 0)).ι).ShortExact := by
    -- The degreewise quotient map gives the exact sequence `0 → K_d → M_d → (M/K)_d → 0`.
    refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
    · simpa [T, i, q] using hExact
    · simpa [T, i] using hi_injective
    · simpa [T, q] using hq_surjective
  -- Apply the Grothendieck-group defining relation to the degreewise short exact sequence.
  simpa [T, gradedPieceFiniteGrothendieckGroupClass, finiteGrothendieckGroupOf]
    using ModulePropertyK0.of_shortExact (R := 𝒜 0) (P := ModuleCat.isFG (𝒜 0)) T hT

/-- Helper for Proposition 10.58.7: the degreewise short exact sequence for a homogeneous
submodule can also be read as a first-difference identity in `K'_0(S₀)`. -/
lemma homogeneous_submodule_degreewise_k0_sub
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    [Module.Finite S M] [Algebra.FiniteType (𝒜 0) S]
    {K : Submodule S M}
    (hK : K.IsHomogeneous ℳ)
    (d : ℤ) :
    gradedPieceFiniteGrothendieckGroupClass 𝒜 ℳ d -
        finiteGrothendieckGroupOf (𝒜 0)
          (homogeneous_submodule_degree_piece_fgModuleCat (𝒜 := 𝒜) (ℳ := ℳ) K d) =
      finiteGrothendieckGroupOf (𝒜 0)
        (homogeneous_quotient_degree_piece_fgModuleCat (𝒜 := 𝒜) (ℳ := ℳ) K d) := by
  -- Rearrange the additive relation into the subtraction form used by first-difference arguments.
  calc
    gradedPieceFiniteGrothendieckGroupClass 𝒜 ℳ d -
        finiteGrothendieckGroupOf (𝒜 0)
          (homogeneous_submodule_degree_piece_fgModuleCat (𝒜 := 𝒜) (ℳ := ℳ) K d) =
      (finiteGrothendieckGroupOf (𝒜 0)
          (homogeneous_submodule_degree_piece_fgModuleCat (𝒜 := 𝒜) (ℳ := ℳ) K d) +
        finiteGrothendieckGroupOf (𝒜 0)
          (homogeneous_quotient_degree_piece_fgModuleCat (𝒜 := 𝒜) (ℳ := ℳ) K d)) -
        finiteGrothendieckGroupOf (𝒜 0)
          (homogeneous_submodule_degree_piece_fgModuleCat (𝒜 := 𝒜) (ℳ := ℳ) K d) := by
            rw [homogeneous_submodule_degreewise_k0_add
              (𝒜 := 𝒜) (ℳ := ℳ) hK d]
    _ = finiteGrothendieckGroupOf (𝒜 0)
          (homogeneous_quotient_degree_piece_fgModuleCat (𝒜 := 𝒜) (ℳ := ℳ) K d) := by
            abel

end
