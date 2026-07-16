import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_71_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Category
open CategoryTheory.Limits
open ChainComplex
open HomologicalComplex

universe u v

noncomputable section

section

variable {R : Type u} [Ring R]
variable {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {F G : ChainComplex (ModuleCat R) ℕ}

local notation "moduleSingle[" M "]" =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/-- Helper for Lemma 10.71.4: every free term of the source complex is projective in
`ModuleCat R`. -/
lemma termwise_projective (hFfree : ChainComplex.IsTermwiseFree F) (n : ℕ) :
    Projective (F.X n) := by
  -- Convert termwise freeness into the projectivity used by the lifting lemmas.
  let _ : Module.Free R (F.X n) := hFfree n
  infer_instance

/-- Helper for Lemma 10.71.4: the degree-`0` augmentation cofork is a cokernel cofork. -/
lemma quasiIso_single_zero_isColimitCokernelCofork_exists
    (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] :
    Nonempty (IsColimit (CokernelCofork.ofπ (πG.f 0) (by simpa using (πG.comm 1 0).symm))) := by
  -- Transport the canonical cokernel description of `opcycles` along the quasi-isomorphism in
  -- degree `0`.
  refine ⟨IsColimit.ofIsoColimit (G.opcyclesIsCokernel 1 0 (by simp)) ?_⟩
  refine Cofork.ext (G.isoHomologyι₀.symm ≪≫ isoOfQuasiIsoAt πG 0 ≪≫
    singleObjHomologySelfIso _ _ _) ?_
  rw [← cancel_mono (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 _).inv,
    ← cancel_mono (ChainComplex.isoHomologyι₀ _).hom]
  dsimp
  simp only [ChainComplex.isoHomologyι₀_inv_naturality_assoc, p_opcyclesMap_assoc,
    single₀_obj_zero, assoc, Iso.hom_inv_id, comp_id, isoHomologyι_inv_hom_id,
    singleObjHomologySelfIso_inv_homologyι, singleObjOpcyclesSelfIso_hom, single₀ObjXSelf,
    Iso.refl_inv, id_comp]

/-- Helper for Lemma 10.71.4: a quasi-isomorphism to `single₀` identifies degree `0` with the
cokernel of the first differential. -/
noncomputable abbrev quasiIso_single_zero_isColimitCokernelCofork
    (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] :
    IsColimit (CokernelCofork.ofπ (πG.f 0) (by simpa using (πG.comm 1 0).symm)) :=
  Classical.choice (quasiIso_single_zero_isColimitCokernelCofork_exists (R := R) (N := N) (G := G) πG)

/-- Helper for Lemma 10.71.4: the augmentation at degree `0` is an epimorphism. -/
lemma quasiIso_single_epi_zero (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] :
    Epi (πG.f 0) := by
  -- The cokernel description at degree `0` gives the required epimorphism.
  simpa using Limits.epi_of_isColimit_cofork
    (quasiIso_single_zero_isColimitCokernelCofork (πG := πG))

/-- Helper for Lemma 10.71.4: the degree-`0` augmentation is available to typeclass search as an
epimorphism. -/
instance quasiIso_single_epi_zero_inst (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] :
    Epi (πG.f 0) :=
  quasiIso_single_epi_zero (R := R) (N := N) (G := G) πG

/-- Helper for Lemma 10.71.4: the short complex `G₁ ⟶ G₀ ⟶ N` is exact. -/
lemma quasiIso_single_exact_zero (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] :
    (ShortComplex.mk (G.d 1 0) (πG.f 0) (by simpa using (πG.comm 1 0).symm)).Exact := by
  -- Exactness at degree `0` follows from the cokernel description above.
  exact ShortComplex.exact_of_g_is_cokernel _ <|
    quasiIso_single_zero_isColimitCokernelCofork (πG := πG)

/-- Helper for Lemma 10.71.4: a quasi-isomorphism to `single₀` makes the target exact in every
positive degree. -/
lemma quasiIso_single_exact_succ (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] (n : ℕ) :
    (ShortComplex.mk (G.d (n + 2) (n + 1)) (G.d (n + 1) n)
      (G.d_comp_d (n + 2) (n + 1) n)).Exact := by
  -- Away from degree `0`, the single complex is exact, so quasi-isomorphism transfers exactness
  -- back to `G`.
  have hExactAt : G.ExactAt (n + 1) :=
    (quasiIsoAt_iff_exactAt' πG (n + 1)
      (ChainComplex.exactAt_succ_single_obj (ModuleCat.of R N) n)).1 inferInstance
  exact
    ((HomologicalComplex.exactAt_iff' G (n + 2) (n + 1) n) (by simp only [prev]; rfl)
      (by simp)).1 hExactAt

/-- Helper for Lemma 10.71.4: choose the degree-`0` component of the lift by factoring through
the augmentation of the target resolution. -/
lemma lift_zero_component_exists
    (f : ModuleCat.of R M ⟶ ModuleCat.of R N)
    (πF : F ⟶ moduleSingle[M]) (πG : G ⟶ moduleSingle[N])
    [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F) :
    ∃ g : F.X 0 ⟶ G.X 0, g ≫ πG.f 0 = πF.f 0 ≫ f := by
  -- Projectivity of `F₀` and surjectivity of `G₀ ⟶ N` give the first lift.
  let g : F.X 0 ⟶ G.X 0 :=
    @Projective.factorThru (ModuleCat R) _ (F.X 0) (ModuleCat.of R N) (G.X 0)
      (termwise_projective (F := F) (R := R) hFfree 0)
      (πF.f 0 ≫ f) (πG.f 0)
      (quasiIso_single_epi_zero (R := R) (N := N) (G := G) πG)
  refine ⟨g, ?_⟩
  simpa [g] using
    (@Projective.factorThru_comp (ModuleCat R) _ (F.X 0) (ModuleCat.of R N) (G.X 0)
      (termwise_projective (F := F) (R := R) hFfree 0)
      (πF.f 0 ≫ f) (πG.f 0)
      (quasiIso_single_epi_zero (R := R) (N := N) (G := G) πG))

/-- Helper for Lemma 10.71.4: choose the degree-`0` component of the lift by factoring through
the augmentation of the target resolution. -/
noncomputable abbrev lift_zero_component
    (f : ModuleCat.of R M ⟶ ModuleCat.of R N)
    (πF : F ⟶ moduleSingle[M]) (πG : G ⟶ moduleSingle[N])
    [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F) :
    F.X 0 ⟶ G.X 0 :=
  Classical.choose (lift_zero_component_exists (R := R) (M := M) (N := N) (F := F) (G := G)
    f πF πG hFfree)

/-- Helper for Lemma 10.71.4: the degree-`0` lift is compatible with the augmentations. -/
lemma lift_zero_component_comp
    (f : ModuleCat.of R M ⟶ ModuleCat.of R N)
    (πF : F ⟶ moduleSingle[M]) (πG : G ⟶ moduleSingle[N])
    [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F) :
    lift_zero_component (R := R) (M := M) (N := N) (F := F) (G := G) f πF πG hFfree ≫ πG.f 0 =
      πF.f 0 ≫ f := by
  -- This is the chosen factorization equation from the previous existence lemma.
  exact Classical.choose_spec (lift_zero_component_exists (R := R) (M := M) (N := N)
    (F := F) (G := G) f πF πG hFfree)

/-- Helper for Lemma 10.71.4: the degree-`1` obstruction lands in the kernel of the augmentation
of `G₀`. -/
lemma lift_one_component_condition
    (f : ModuleCat.of R M ⟶ ModuleCat.of R N)
    (πF : F ⟶ moduleSingle[M]) (πG : G ⟶ moduleSingle[N])
    [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F) :
    F.d 1 0 ≫ lift_zero_component (R := R) (M := M) (N := N) (F := F) (G := G) f πF πG hFfree ≫
        πG.f 0 = 0 := by
  -- Compatibility of the degree-`0` lift with the augmentations kills the obstruction.
  have h :=
    congrArg (fun k ↦ F.d 1 0 ≫ k)
      (lift_zero_component_comp (R := R) (M := M) (N := N) (F := F) (G := G)
        f πF πG hFfree)
  have hπ : F.d 1 0 ≫ πF.f 0 = 0 := by
    simpa using (πF.comm 1 0).symm
  calc
    F.d 1 0 ≫ lift_zero_component (R := R) (M := M) (N := N) (F := F) (G := G) f πF πG
        hFfree ≫ πG.f 0 =
      F.d 1 0 ≫ πF.f 0 ≫ f := by
        simpa [Category.assoc] using h
    _ = 0 := by
        exact (congrArg (fun k ↦ k ≫ f) hπ).trans <|
          (Limits.zero_comp : (0 : F.X 1 ⟶ ModuleCat.of R M) ≫ f = 0)

/-- Helper for Lemma 10.71.4: exactness at degree `0` lifts the first obstruction into degree
`1`. -/
noncomputable abbrev lift_one_component
    (f : ModuleCat.of R M ⟶ ModuleCat.of R N)
    (πF : F ⟶ moduleSingle[M]) (πG : G ⟶ moduleSingle[N])
    [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F) :
    F.X 1 ⟶ G.X 1 :=
  letI : Projective (F.X 1) := termwise_projective (F := F) (R := R) hFfree 1
  (quasiIso_single_exact_zero (R := R) (N := N) (G := G) πG).liftFromProjective
    (F.d 1 0 ≫ lift_zero_component (R := R) (M := M) (N := N) (F := F) (G := G) f πF πG hFfree)
    (lift_one_component_condition (R := R) (M := M) (N := N) (F := F) (G := G)
      f πF πG hFfree)

/-- Helper for Lemma 10.71.4: the lifted degree-`1` component commutes with the differentials. -/
lemma lift_one_component_comm
    (f : ModuleCat.of R M ⟶ ModuleCat.of R N)
    (πF : F ⟶ moduleSingle[M]) (πG : G ⟶ moduleSingle[N])
    [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F) :
    lift_one_component (R := R) (M := M) (N := N) (F := F) (G := G) f πF πG hFfree ≫ G.d 1 0 =
      F.d 1 0 ≫ lift_zero_component (R := R) (M := M) (N := N) (F := F) (G := G)
        f πF πG hFfree := by
  -- This is the defining equation of the exactness lift at degree `0`.
  letI : Projective (F.X 1) := termwise_projective (F := F) (R := R) hFfree 1
  exact (quasiIso_single_exact_zero (R := R) (N := N) (G := G) πG).liftFromProjective_comp _ _

/-- Helper for Lemma 10.71.4: exactness in positive degrees lifts each successive obstruction. -/
noncomputable abbrev lift_obstruction_through_exact_succ
    (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F)
    (n : ℕ) (g : F.X n ⟶ G.X n) (g' : F.X (n + 1) ⟶ G.X (n + 1))
    (w : g' ≫ G.d (n + 1) n = F.d (n + 1) n ≫ g) :
    Σ' g'' : F.X (n + 2) ⟶ G.X (n + 2),
      g'' ≫ G.d (n + 2) (n + 1) = F.d (n + 2) (n + 1) ≫ g' :=
  letI : Projective (F.X (n + 2)) := termwise_projective (F := F) (R := R) hFfree (n + 2)
  ⟨(quasiIso_single_exact_succ (R := R) (N := N) (G := G) πG n).liftFromProjective
      (F.d (n + 2) (n + 1) ≫ g') (by simp [w]),
    (quasiIso_single_exact_succ (R := R) (N := N) (G := G) πG n).liftFromProjective_comp _ _⟩

/-- Helper for Lemma 10.71.4: if `γ` dies after augmentation, its degree-`0` component lifts
through `G₁ ⟶ G₀`. -/
noncomputable abbrev nullhomotopy_zero_component
    (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F)
    (γ : F ⟶ G) (hγ : γ ≫ πG = 0) :
    F.X 0 ⟶ G.X 1 :=
  letI : Projective (F.X 0) := termwise_projective (F := F) (R := R) hFfree 0
  (quasiIso_single_exact_zero (R := R) (N := N) (G := G) πG).liftFromProjective
    (γ.f 0) (congr_fun (congr_arg HomologicalComplex.Hom.f hγ) 0)

/-- Helper for Lemma 10.71.4: the degree-`0` homotopy component kills `γ.f 0`. -/
lemma nullhomotopy_zero_component_comp
    (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F)
    (γ : F ⟶ G) (hγ : γ ≫ πG = 0) :
    nullhomotopy_zero_component (R := R) (N := N) (F := F) (G := G) πG hFfree γ hγ ≫ G.d 1 0 =
      γ.f 0 := by
  -- This is the defining property of the exactness lift at degree `0`.
  letI : Projective (F.X 0) := termwise_projective (F := F) (R := R) hFfree 0
  exact (quasiIso_single_exact_zero (R := R) (N := N) (G := G) πG).liftFromProjective_comp _ _

/-- Helper for Lemma 10.71.4: after correcting degree `0`, the degree-`1` obstruction is a
cycle in `G₁`. -/
lemma nullhomotopy_one_component_condition
    (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F)
    (γ : F ⟶ G) (hγ : γ ≫ πG = 0) :
    (γ.f 1 - F.d 1 0 ≫
        nullhomotopy_zero_component (R := R) (N := N) (F := F) (G := G) πG hFfree γ hγ) ≫
        G.d 1 0 = 0 := by
  -- The chain map identity and the degree-`0` correction cancel the boundary.
  rw [Preadditive.sub_comp, assoc, nullhomotopy_zero_component_comp, γ.comm]
  simp

/-- Helper for Lemma 10.71.4: after correcting by the degree-`0` homotopy component, the degree-`1`
obstruction lifts into `G₂`. -/
noncomputable abbrev nullhomotopy_one_component
    (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F)
    (γ : F ⟶ G) (hγ : γ ≫ πG = 0) :
    F.X 1 ⟶ G.X 2 :=
  letI : Projective (F.X 1) := termwise_projective (F := F) (R := R) hFfree 1
  (quasiIso_single_exact_succ (R := R) (N := N) (G := G) πG 0).liftFromProjective
    (γ.f 1 - F.d 1 0 ≫
      nullhomotopy_zero_component (R := R) (N := N) (F := F) (G := G) πG hFfree γ hγ)
    (nullhomotopy_one_component_condition (R := R) (N := N) (F := F) (G := G) πG hFfree γ hγ)

/-- Helper for Lemma 10.71.4: the degree-`1` homotopy component gives the required correction in
degree `1`. -/
lemma nullhomotopy_one_component_comp
    (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F)
    (γ : F ⟶ G) (hγ : γ ≫ πG = 0) :
    nullhomotopy_one_component (R := R) (N := N) (F := F) (G := G) πG hFfree γ hγ ≫ G.d 2 1 =
      γ.f 1 - F.d 1 0 ≫
        nullhomotopy_zero_component (R := R) (N := N) (F := F) (G := G) πG hFfree γ hγ := by
  -- This is the defining equation of the lift through `G₂ ⟶ G₁`.
  letI : Projective (F.X 1) := termwise_projective (F := F) (R := R) hFfree 1
  exact (quasiIso_single_exact_succ (R := R) (N := N) (G := G) πG 0).liftFromProjective_comp _ _

/-- Helper for Lemma 10.71.4: after two consecutive homotopy components are fixed, exactness in
positive degrees lifts the next corrected obstruction. -/
lemma nullhomotopy_succ_component_condition
    (πG : G ⟶ moduleSingle[N]) [QuasiIso πG]
    (γ : F ⟶ G) (n : ℕ) (g : F.X n ⟶ G.X (n + 1)) (g' : F.X (n + 1) ⟶ G.X (n + 2))
    (w : γ.f (n + 1) = F.d (n + 1) n ≫ g + g' ≫ G.d (n + 2) (n + 1)) :
    (γ.f (n + 2) - F.d (n + 2) (n + 1) ≫ g') ≫ G.d (n + 2) (n + 1) = 0 := by
  -- The inductive correction produces a cycle exactly as in the textbook recurrence.
  rw [Preadditive.sub_comp, γ.comm, w]
  simp [assoc]

/-- Helper for Lemma 10.71.4: after two consecutive homotopy components are fixed, exactness in
positive degrees lifts the next corrected obstruction. -/
noncomputable abbrev nullhomotopy_succ_component
    (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F)
    (γ : F ⟶ G) (n : ℕ) (g : F.X n ⟶ G.X (n + 1)) (g' : F.X (n + 1) ⟶ G.X (n + 2))
    (w : γ.f (n + 1) = F.d (n + 1) n ≫ g + g' ≫ G.d (n + 2) (n + 1)) :
    F.X (n + 2) ⟶ G.X (n + 3) :=
  letI : Projective (F.X (n + 2)) := termwise_projective (F := F) (R := R) hFfree (n + 2)
  (quasiIso_single_exact_succ (R := R) (N := N) (G := G) πG (n + 1)).liftFromProjective
    (γ.f (n + 2) - F.d (n + 2) (n + 1) ≫ g')
    (nullhomotopy_succ_component_condition (R := R) (N := N) (F := F) (G := G)
      πG γ n g g' w)

/-- Helper for Lemma 10.71.4: the successor homotopy component satisfies the inductive
correction identity. -/
lemma nullhomotopy_succ_component_comp
    (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F)
    (γ : F ⟶ G) (n : ℕ) (g : F.X n ⟶ G.X (n + 1)) (g' : F.X (n + 1) ⟶ G.X (n + 2))
    (w : γ.f (n + 1) = F.d (n + 1) n ≫ g + g' ≫ G.d (n + 2) (n + 1)) :
    nullhomotopy_succ_component (R := R) (N := N) (F := F) (G := G) πG hFfree γ n g g' w ≫
        G.d (n + 3) (n + 2) =
      γ.f (n + 2) - F.d (n + 2) (n + 1) ≫ g' := by
  -- This is the defining equation of the positive-degree lift.
  letI : Projective (F.X (n + 2)) := termwise_projective (F := F) (R := R) hFfree (n + 2)
  exact (quasiIso_single_exact_succ (R := R) (N := N) (G := G) πG (n + 1)).liftFromProjective_comp _ _

/-- Lemma 10.71.4 (1): for a map `M ⟶ N`, a resolution `πG : G ⟶ N`, and a chain complex
`πF : F ⟶ M` of free `R`-modules, there exists a chain map `F ⟶ G` compatible with the
augmentations. -/
-- Proof sketch: construct the lift degreewise using projectivity of the free source terms.
-- This is the same inductive lifting pattern as the owner construction
-- `ProjectiveResolution.lift`, specialized to a source complex that need not itself resolve `M`.
-- Since `F.X 0` is free, lift the composite `F.X 0 ⟶ M ⟶ N` through `πG.f 0`. Inductively,
-- exactness of `G` in positive degrees shows that the obstruction to extending the partial lift
-- lands in the image of the next differential, and the termwise-free hypothesis on `F` allows one
-- to lift through that differential in each degree.
@[stacks 00LS]
lemma free_complex_lift_to_resolution_exists
    (f : ModuleCat.of R M ⟶ ModuleCat.of R N)
    (πF : F ⟶ moduleSingle[M])
    (πG : G ⟶ moduleSingle[N])
    [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F) :
    ∃ α : F ⟶ G, α ≫ πG = πF ≫ (ChainComplex.single₀ (ModuleCat R)).map f := by
  -- Build the lift degreewise: degree `0`, degree `1`, and then the inductive successor step.
  refine ⟨ChainComplex.mkHom _ _
      (lift_zero_component (R := R) (M := M) (N := N) (F := F) (G := G) f πF πG hFfree)
      (lift_one_component (R := R) (M := M) (N := N) (F := F) (G := G) f πF πG hFfree)
      (lift_one_component_comm (R := R) (M := M) (N := N) (F := F) (G := G) f πF πG hFfree)
      (fun n p ↦
        lift_obstruction_through_exact_succ (R := R) (N := N) (F := F) (G := G) πG hFfree n
          p.1 p.2.1 p.2.2), ?_⟩
  -- The constructed chain map is compatible with the augmentations: degree `0` is by construction,
  -- and all positive degrees vanish against the single complex.
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
      simpa using lift_zero_component_comp (R := R) (M := M) (N := N) (F := F) (G := G)
        f πF πG hFfree
  | succ n =>
      apply IsZero.eq_of_tgt
      apply HomologicalComplex.isZero_single_obj_X
      simp

/-- Lemma 10.71.4 (2): any two augmentation-compatible lifts from a free chain complex to a
resolution are homotopic. -/
-- Proof sketch: subtract the two lifts to reduce to a chain map `γ : F ⟶ G` with `γ ≫ πG = 0`.
-- The same inductive construction that underlies `ProjectiveResolution.liftHomotopy` then
-- yields a homotopy between `α` and `β`. Lift `γ.f 0` through `G.d 1 0` using exactness at
-- degree `0`, then inductively correct `γ.f (n + 1)` by the previously constructed homotopy
-- component and lift the remainder through `G.d (n + 2) (n + 1)` using exactness and the
-- termwise-free hypothesis on `F`.
@[stacks 00LS]
theorem free_complex_lifts_to_resolution_are_homotopic
    (f : ModuleCat.of R M ⟶ ModuleCat.of R N)
    (πF : F ⟶ moduleSingle[M])
    (πG : G ⟶ moduleSingle[N])
    [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F)
    {α β : F ⟶ G}
    (hα : α ≫ πG = πF ≫ (ChainComplex.single₀ (ModuleCat R)).map f)
    (hβ : β ≫ πG = πF ≫ (ChainComplex.single₀ (ModuleCat R)).map f) :
    homotopic (ModuleCat R) (ComplexShape.down ℕ) α β := by
  -- Subtract the two compatible lifts and construct a null-homotopy of the difference.
  let γ : F ⟶ G := α - β
  have hγ : γ ≫ πG = 0 := by
    simp [γ, hα, hβ]
  refine ⟨Homotopy.equivSubZero.invFun <|
    Homotopy.mkInductive γ
      (nullhomotopy_zero_component (R := R) (N := N) (F := F) (G := G) πG hFfree γ hγ)
      (by
        have h :=
          nullhomotopy_zero_component_comp
            (R := R) (N := N) (F := F) (G := G) πG hFfree γ hγ
        simpa using h.symm)
      (nullhomotopy_one_component (R := R) (N := N) (F := F) (G := G) πG hFfree γ hγ)
      (by
        have h :=
          nullhomotopy_one_component_comp
            (R := R) (N := N) (F := F) (G := G) πG hFfree γ hγ
        rw [eq_sub_iff_add_eq] at h
        simpa [add_comm, add_left_comm, add_assoc] using h.symm)
      (fun n p ↦
        ⟨nullhomotopy_succ_component (R := R) (N := N) (F := F) (G := G) πG hFfree γ n
            p.1 p.2.1 p.2.2,
          by
            have h :=
              nullhomotopy_succ_component_comp
                (R := R) (N := N) (F := F) (G := G) πG hFfree γ n
                p.1 p.2.1 p.2.2
            rw [eq_sub_iff_add_eq] at h
            simpa [add_comm, add_left_comm, add_assoc] using h.symm⟩)⟩

end
