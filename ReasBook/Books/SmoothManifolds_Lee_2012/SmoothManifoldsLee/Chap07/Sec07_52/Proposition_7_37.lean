import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_52.Definition_7_52_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uH uE uG uV

-- Semantic recall note: `lean_leansearch` is unavailable in this environment. Local project and
-- mathlib inspection identified the source-facing owner `IsLinearAction 𝕜 G V`, the canonical
-- algebraic owner `Representation 𝕜 G V` with constructor `Representation.ofDistribMulAction`,
-- and the smooth owner `ContMDiffMonoidMorphism I 𝓘(𝕜, V →L[𝕜] V) ∞ G (V →L[𝕜] V)ˣ`.

section

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G] [LieGroup I ∞ G]
variable {V : Type uV} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]

/-- A smooth representation of a Lie group `G` on the normed vector space `V`, viewed as a smooth
group homomorphism into the smooth general linear group `(V →L[𝕜] V)ˣ`. -/
abbrev LieGroupRepresentation
    (I : ModelWithCorners 𝕜 E H)
    (G : Type uG) [Group G] [TopologicalSpace G] [ChartedSpace H G] [LieGroup I ∞ G]
    (V : Type uV) [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V] :
    Type _ :=
  ContMDiffMonoidMorphism I 𝓘(𝕜, V →L[𝕜] V) ∞ G (V →L[𝕜] V)ˣ

local notation "LieRep" => LieGroupRepresentation I G V

namespace LieGroupRepresentation

/-- The underlying algebraic representation of a smooth Lie-group representation. -/
noncomputable def toRepresentation (ρ : LieRep) : Representation 𝕜 G V where
  toFun g := (ρ g : V →L[𝕜] V).toLinearMap
  map_one' := by
    ext v
    rw [show (ρ 1 : (V →L[𝕜] V)ˣ) = 1 by exact ρ.map_one]
    rfl
  map_mul' g h := by
    ext v
    rw [show (ρ (g * h) : (V →L[𝕜] V)ˣ) = ρ g * ρ h by exact ρ.map_mul g h]
    rfl

@[simp] theorem toRepresentation_apply (ρ : LieRep) (g : G) (v : V) :
    ρ.toRepresentation g v = (ρ g : V →L[𝕜] V) v :=
  rfl

end LieGroupRepresentation

variable [MulAction G V] [ContMDiffSMul I 𝓘(𝕜, V) ∞ G V] [FiniteDimensional 𝕜 V]

/-- Helper for Proposition 7.37: a nontrivial complete finite-dimensional normed `𝕜`-space forces
`𝕜` itself to be complete. -/
-- TODO: Prove this by a field-completeness bridge from a nontrivial complete finite-dimensional
-- `𝕜`-space. The rest of the proof only uses it to unlock mathlib's finite-dimensional continuity
-- API on `LinearMap` and `ContinuousLinearMap`.
lemma completeSpaceFieldOfCompleteFiniteDimensional
    (V' : Type uV) [NormedAddCommGroup V'] [NormedSpace 𝕜 V'] [CompleteSpace V']
    [FiniteDimensional 𝕜 V'] [Nontrivial V'] : CompleteSpace 𝕜 :=
  sorry

/-- Helper for Proposition 7.37: smoothness of a `ContinuousLinearMap`-valued map is equivalent to
smoothness of all evaluation maps when the source vector space is finite-dimensional. -/
theorem contMDiffContinuousLinearMap_iff_forall_apply
    [CompleteSpace 𝕜]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {V₁ : Type*} [NormedAddCommGroup V₁] [NormedSpace 𝕜 V₁] [FiniteDimensional 𝕜 V₁]
    {W : Type*}
    [NormedAddCommGroup W] [NormedSpace 𝕜 W] {f : M → V₁ →L[𝕜] W} :
    ContMDiff I 𝓘(𝕜, V₁ →L[𝕜] W) ∞ f ↔
      ∀ y : V₁, ContMDiff I 𝓘(𝕜, W) ∞ (fun x ↦ f x y) :=
  -- Route correction: the smoothness step is handled in finite coordinates for `V₁ →L[𝕜] W`,
  -- rather than by expanding the main theorem around the field-completeness detour.
  let d := Module.finrank 𝕜 V₁
  have hd : d = Module.finrank 𝕜 (Fin d → 𝕜) := by
    simpa [d] using (finrank_fin_fun 𝕜).symm
  let e₁ : V₁ ≃L[𝕜] Fin d → 𝕜 :=
    ContinuousLinearEquiv.ofFinrankEq hd
  let e : (V₁ →L[𝕜] W) ≃L[𝕜] Fin d → W :=
    (e₁.arrowCongr (1 : W ≃L[𝕜] W)).trans
      (ContinuousLinearEquiv.piRing (Fin d))
  ⟨fun hf y ↦ by
      -- Evaluate the smooth operator-valued map at the fixed vector `y`.
      exact hf.clm_apply
        (contMDiff_const : ContMDiff I 𝓘(𝕜, V₁) ∞ (fun _ : M ↦ y)),
    fun h ↦ by
      have hpi : ContMDiff I 𝓘(𝕜, Fin d → W) ∞
          (fun x ↦ e (f x)) := by
        -- The coordinate normal form is smooth once each fixed evaluation map is smooth.
        refine contMDiff_pi_space.2 ?_
        intro i
        let y : V₁ := e₁.symm (Pi.single i 1)
        have hy := h y
        simpa [e, e₁, y] using hy
      -- Return from coordinates by composing with the inverse equivalence.
      let eSymm : (Fin d → W) →L[𝕜] (V₁ →L[𝕜] W) := e.symm.toContinuousLinearMap
      have hSymm : ContMDiff 𝓘(𝕜, Fin d → W) 𝓘(𝕜, V₁ →L[𝕜] W) ∞ eSymm :=
        eSymm.contMDiff
      refine (hSymm.comp hpi).congr ?_
      intro x
      simp [eSymm] ⟩

/-- Helper for Proposition 7.37: the algebraic representation attached to a linear action, viewed
inside the units of continuous endomorphisms. -/
noncomputable def linearActionContinuousUnits [CompleteSpace 𝕜] (h : IsLinearAction 𝕜 G V) :
    G →* (V →L[𝕜] V)ˣ :=
  ((Units.mapEquiv (Module.End.toContinuousLinearMap V).toMulEquiv).toMonoidHom).comp
    h.toRepresentation.asGroupHom

/-- Helper for Proposition 7.37: the transported continuous-endomorphism representation acts by the
original group action. -/
@[simp] theorem linearActionContinuousUnits_apply [CompleteSpace 𝕜]
    (h : IsLinearAction 𝕜 G V) (g : G) (v : V) :
    (linearActionContinuousUnits h g : V →L[𝕜] V) v = g • v := by
  -- This collapses the transport from algebraic units to continuous units.
  simp [linearActionContinuousUnits, Representation.asGroupHom_apply,
    Module.End.toContinuousLinearMap, LinearMap.coe_toContinuousLinearMap',
    IsLinearAction.toRepresentation_apply]

/-- Helper for Proposition 7.37: the operator-valued map extracted from a smooth linear action is
smooth. -/
theorem linearActionContinuousUnits_contMDiff [CompleteSpace 𝕜] (h : IsLinearAction 𝕜 G V) :
    ContMDiff I 𝓘(𝕜, V →L[𝕜] V) ∞
      (fun g ↦ (linearActionContinuousUnits h g : V →L[𝕜] V)) := by
  rw [contMDiffContinuousLinearMap_iff_forall_apply]
  intro v
  -- For each fixed vector, the evaluation map is the smooth orbit map.
  simpa using
    (contMDiff_id.smul (contMDiff_const : ContMDiff I 𝓘(𝕜, V) ∞ fun _ : G ↦ v))

/-- Proposition 7.37. For a smooth left action of a Lie group `G` on a finite-dimensional vector
space `V`, the action is linear, in the sense that each action map `v ↦ g • v` is given by a
linear endomorphism of `V`, if and only if it is induced by some smooth representation
`ρ : G → (V →L[𝕜] V)ˣ`, in the sense that `g • v = ρ g • v` for all `g : G` and `v : V`. -/
theorem isLinearAction_iff_exists_lieGroupRepresentation :
    IsLinearAction 𝕜 G V ↔
      ∃ ρ : LieRep, ∀ g : G, ∀ v : V, g • v = ρ.toRepresentation g v := by
  by_cases hV : Subsingleton V
  · constructor
    · intro _
      refine ⟨{ toMonoidHom := 1, contMDiff_toFun := contMDiff_const }, ?_⟩
      intro g v
      exact hV.elim _ _
    · intro hρ
      rcases hρ with ⟨ρ, hρ⟩
      refine ⟨?_, ?_⟩
      · intro g v w
        exact hV.elim _ _
      · intro g a v
        exact hV.elim _ _
  · letI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
    letI : CompleteSpace 𝕜 := completeSpaceFieldOfCompleteFiniteDimensional V
    constructor
    · intro h
      let ρu := linearActionContinuousUnits h
      have hρu :
          ContMDiff I 𝓘(𝕜, V →L[𝕜] V) ∞ (fun g ↦ (ρu g : V →L[𝕜] V)) := by
        simpa [ρu] using linearActionContinuousUnits_contMDiff h
      refine ⟨{ toMonoidHom := ρu, contMDiff_toFun := ?_ }, ?_⟩
      · -- Lift smoothness from the ambient operator space to the units manifold.
        simpa using ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val hρu
      · intro g v
        -- The packaged smooth representation is the transported algebraic one.
        rw [LieGroupRepresentation.toRepresentation_apply]
        exact (linearActionContinuousUnits_apply h g v).symm
    · rintro ⟨ρ, hρ⟩
      refine ⟨?_, ?_⟩
      · intro g v w
        -- Rewrite the action through the representation and use linearity of `ρ g`.
        rw [hρ g (v + w), hρ g v, hρ g w]
        simpa using (ρ.toRepresentation g).map_add v w
      · intro g a v
        -- Scalar compatibility is exactly the linearity of the representation operator.
        rw [hρ g (a • v), hρ g v]
        simpa using (ρ.toRepresentation g).map_smul a v

end
