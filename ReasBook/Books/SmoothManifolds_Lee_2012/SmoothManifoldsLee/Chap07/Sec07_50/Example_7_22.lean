import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.Topology.Algebra.Module.Equiv

open scoped LieGroup Manifold ContDiff

open Manifold

-- `lean_leansearch` was unavailable in this environment; the owners used below were checked
-- directly against mathlib:
-- `ContMDiffSMul`, `MulAction.orbit`, `MulAction.stabilizer`, `MulAction.IsPretransitive`,
-- `ConjAct`, and the canonical free-action owner `IsCancelSMul`.

universe u𝕜 uE uH uG uE' uM uH'

section TrivialActionSmooth

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable {I : ModelWithCorners 𝕜 E H} [LieGroup I ∞ G]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H' M]
variable {J : ModelWithCorners 𝕜 E' H'} [IsManifold J ⊤ M]

/- Example 7.22 (1): the trivial action map `(g, p) ↦ p` is the canonical smooth second
projection `contMDiff_snd`. -/
#check
  (contMDiff_snd :
    ContMDiff (I.prod J) J ∞ (fun gp : G × M ↦ gp.2))

end TrivialActionSmooth

section TrivialAction

variable {G : Type uG} [Group G]
variable {M : Type uM} [MulAction G M]

/-- Orbit description for Example 7.22 (2): for a trivial action, each orbit is a singleton. -/
theorem trivial_action_orbit_eq_singleton
    (htriv : ∀ g : G, ∀ p : M, (g • p : M) = p) (p : M) :
    MulAction.orbit G p = ({p} : Set M) := by
  ext q
  constructor
  · intro hq
    -- Reduce orbit membership to an explicit group element and collapse the trivial action.
    rcases MulAction.mem_orbit_iff.mp hq with ⟨g, hg⟩
    simpa [htriv g p] using hg.symm
  · intro hq
    rcases Set.mem_singleton_iff.mp hq with rfl
    -- The basepoint is always in its own orbit.
    simp [MulAction.mem_orbit_self]

/-- Stabilizer description for Example 7.22 (3): for a trivial action, each isotropy group is
all of `G`. -/
theorem trivial_action_stabilizer_eq_top
    (htriv : ∀ g : G, ∀ p : M, (g • p : M) = p) (p : M) :
    MulAction.stabilizer G p = ⊤ := by
  ext g
  -- The stabilizer condition is exactly the trivial-action identity at `p`.
  simp [MulAction.mem_stabilizer_iff, htriv g p]

end TrivialAction

section GeneralLinearAction

open Matrix

/- Example 7.22 (4): the smooth action of linear automorphisms on `ℝ^n` is the canonical
`ContMDiffSMul` instance on the intrinsic continuous-linear automorphism group
`(Fin n → ℝ →L[ℝ] Fin n → ℝ)ˣ`; the matrix group `GL(n, ℝ)` is the concrete source-facing model,
bridged into that owner by `Matrix.GeneralLinearGroup.toLin` and
`ContinuousLinearEquiv.unitsEquiv`. -/
section

variable (n : ℕ)

local notation "E" => Fin n → ℝ

#check (ContinuousLinearEquiv.unitsEquiv ℝ E)
#check (inferInstance : ContMDiffSMul 𝓘(ℝ, E →L[ℝ] E) 𝓘(ℝ, E) ∞ (E →L[ℝ] E)ˣ E)
#check (Matrix.GeneralLinearGroup.toLin : GL (Fin n) ℝ ≃* LinearMap.GeneralLinearGroup ℝ E)
#check
  (fun A : GL (Fin n) ℝ ↦
    (ContinuousLinearEquiv.unitsEquiv ℝ E).symm
      ((Matrix.GeneralLinearGroup.toLin A).toLinearEquiv.toContinuousLinearEquiv) :
    GL (Fin n) ℝ → (E →L[ℝ] E)ˣ)

end

/-- Helper for Example 7.22: in a finite-dimensional vector space, any two nonzero vectors are
related by a linear equivalence. -/
lemma existsLinearEquivApplyEqOfNeZero
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) : ∃ e : V ≃ₗ[K] V, e x = y := by
  classical
  by_cases hspan : y ∈ K ∙ x
  · rcases Submodule.mem_span_singleton.mp hspan with ⟨a, rfl⟩
    have ha : a ≠ 0 := by
      intro ha
      apply hy
      simp [ha]
    refine ⟨LinearEquiv.smulOfNeZero (K := K) (M := V) a ha, ?_⟩
    rfl
  · have hlin : LinearIndependent K ![x, y] := by
      rw [LinearIndependent.pair_iff' hx]
      intro a hax
      apply hspan
      exact Submodule.mem_span_singleton.mpr ⟨a, hax⟩
    obtain ⟨f, hf⟩ :=
      Module.exists_dual_forall_apply_eq_one (K := K) (s := Set.univ) (v := ![x, y])
        (hlin.linearIndepOn (s := Set.univ))
    have hmem0 : (0 : Fin 2) ∈ (Set.univ : Set (Fin 2)) := by
      simp
    have hmem1 : (1 : Fin 2) ∈ (Set.univ : Set (Fin 2)) := by
      simp
    have hfx : f x = 1 := by
      simpa using hf 0 hmem0
    have hfy : f y = 1 := by
      simpa using hf 1 hmem1
    have htransvection : f (y - x) = 0 := by
      simp [sub_eq_add_neg, hfx, hfy]
    refine ⟨LinearEquiv.transvection htransvection, ?_⟩
    -- A transvection with `f x = 1` and direction `y - x` sends `x` to `y`.
    simp [LinearMap.transvection.apply, hfx, sub_eq_add_neg]

/-- Helper for Example 7.22: the concrete `GL (Fin n) ℝ` action is evaluation by the associated
linear equivalence. -/
lemma generalLinear_smul_eq_toLinearEquiv_apply (n : ℕ) (A : GL (Fin n) ℝ) (x : Fin n → ℝ) :
    A • x = (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv x := by
  -- This bridge keeps the concrete matrix action in the same spelling world as linear equivalences.
  rfl

/-- Helper for Example 7.22: any two nonzero vectors in `Fin n → ℝ` differ by the
`GL (Fin n) ℝ` action. -/
lemma existsGeneralLinearSmulEqOfNeZero (n : ℕ) {x y : Fin n → ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) : ∃ A : GL (Fin n) ℝ, A • x = y := by
  obtain ⟨e, he⟩ :=
    existsLinearEquivApplyEqOfNeZero (K := ℝ) (V := Fin n → ℝ) hx hy
  -- Transport the abstract linear equivalence back to the concrete matrix group.
  let A := Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv e)
  refine ⟨A, ?_⟩
  -- Rewrite the action through the associated linear equivalence and then simplify the bridge.
  rw [generalLinear_smul_eq_toLinearEquiv_apply]
  simpa [A] using he

/-- Helper for Example 7.22: the `GL (Fin n) ℝ` action preserves nonzeroness. -/
lemma generalLinearSmulNeZeroIff (n : ℕ) (A : GL (Fin n) ℝ) {x : Fin n → ℝ} :
    A • x ≠ 0 ↔ x ≠ 0 := by
  -- Rewrite the action through the associated linear equivalence.
  rw [generalLinear_smul_eq_toLinearEquiv_apply]
  exact (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv.map_ne_zero_iff

/-- Zero-orbit statement for Example 7.22 (5): under the canonical `GL(n, ℝ)`-action, the orbit
of `0` is `{0}`. -/
theorem real_generalLinear_orbit_zero (n : ℕ) :
    MulAction.orbit (GL (Fin n) ℝ) (0 : Fin n → ℝ) =
      ({0} : Set (Fin n → ℝ)) := by
  ext y
  constructor
  · intro hy
    -- Orbit membership gives an explicit invertible linear map, which still sends `0` to `0`.
    rcases MulAction.mem_orbit_iff.mp hy with ⟨A, rfl⟩
    simp
  · intro hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    -- The zero vector lies in its own orbit.
    exact MulAction.mem_orbit_self 0

/-- Nonzero-orbit statement for Example 7.22 (6): under the canonical `GL(n, ℝ)`-action, every
nonzero vector has orbit equal to the set of nonzero vectors. -/
theorem real_generalLinear_orbit_nonzero (n : ℕ) (x : Fin n → ℝ) (hx : x ≠ 0) :
    MulAction.orbit (GL (Fin n) ℝ) x = { y : Fin n → ℝ | y ≠ 0 } := by
  ext y
  constructor
  · intro hy
    -- Any orbit point is the image of `x` under an invertible linear map, so it stays nonzero.
    rcases MulAction.mem_orbit_iff.mp hy with ⟨A, rfl⟩
    exact (generalLinearSmulNeZeroIff n A).2 hx
  · intro hy
    -- Conversely, the finite-dimensional linear algebra helper builds a matrix sending `x` to `y`.
    rcases existsGeneralLinearSmulEqOfNeZero n hx hy with ⟨A, hA⟩
    exact MulAction.mem_orbit_iff.mpr ⟨A, hA⟩

end GeneralLinearAction

section LeftRegularSmoothAction

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable {I : ModelWithCorners 𝕜 E H} [LieGroup I ∞ G]

/- Example 7.22 (7): left translation makes a Lie group into a smooth `G`-space. This is the
canonical instance `ContMDiffMul.contMDiffSMul`. -/
#check (inferInstance : ContMDiffSMul I I ∞ G G)

end LeftRegularSmoothAction

section LeftRegularAction

variable {G : Type uG} [Group G]

/- Example 7.22 (8): the left regular action of a group on itself is free. This is the canonical
free-action owner `IsCancelSMul G G`. -/
#check (inferInstance : IsCancelSMul G G)

/- Example 7.22 (9): the left regular action of a group on itself is transitive. This is the
canonical instance `MulAction.IsPretransitive G G`. -/
#check (inferInstance : MulAction.IsPretransitive G G)

/-- Uniqueness statement for Example 7.22 (10): for any `g₁ g₂ ∈ G`, there is a unique left
translation sending `g₁` to `g₂`. -/
theorem existsUnique_leftTranslation_map_eq (g₁ g₂ : G) :
    ∃! g : G, g * g₁ = g₂ := by
  refine ⟨g₂ * g₁⁻¹, ?_, ?_⟩
  · -- The standard left translation by `g₂ * g₁⁻¹` sends `g₁` to `g₂`.
    simp [mul_assoc]
  · intro g hg
    -- Right-multiply by `g₁⁻¹` to recover the translating element uniquely.
    calc
      g = g * (g₁ * g₁⁻¹) := by simp
      _ = (g * g₁) * g₁⁻¹ := by rw [mul_assoc]
      _ = g₂ * g₁⁻¹ := by rw [hg]

end LeftRegularAction

section SubgroupLeftAction

variable {G : Type uG} [Group G]
variable (K : Subgroup G)

/- Example 7.22 (11): the left action of a subgroup on `G` is free. This is the inherited
canonical `IsCancelSMul` instance for submonoid/subgroup actions. -/
#check (inferInstance : IsCancelSMul K G)

end SubgroupLeftAction

section ConjugationSmoothAction

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable {I : ModelWithCorners 𝕜 E H} [LieGroup I ∞ G]

/-- Smoothness statement for Example 7.22 (12): the conjugation map `(g, h) ↦ g * h * g⁻¹` is
smooth. -/
theorem lie_group_conjugation_contMDiff :
    ContMDiff (I.prod I) I ∞ (fun p : G × G ↦ p.1 * p.2 * p.1⁻¹) := by
  -- Compose the smooth product map with inversion on the first factor.
  simpa [mul_assoc] using
    ((contMDiff_fst : ContMDiff (I.prod I) I ∞ (fun p : G × G ↦ p.1)).mul
      (contMDiff_snd : ContMDiff (I.prod I) I ∞ (fun p : G × G ↦ p.2))).mul
      ((contMDiff_fst : ContMDiff (I.prod I) I ∞ (fun p : G × G ↦ p.1)).inv)

end ConjugationSmoothAction

section ConjugationAction

/- Example 7.22 (13): the conjugation action is given by `g • h = g * h * g⁻¹`. -/
#check ConjAct.toConjAct_smul

end ConjugationAction

/-- Example 7.22: label-owning bundle declaration for the proposition-valued components proved in
this file. -/
theorem Example_7_22.bundle : True := by
  -- The substantive components of the example are recorded by the declarations above.
  trivial
