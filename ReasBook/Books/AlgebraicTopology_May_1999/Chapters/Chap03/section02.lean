import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_3_2_1 (from Chap03) -/
open scoped unitInterval

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

namespace IsPathConnectedCoveringMap

variable {p : E → B}

/-- Theorem 3.2.1: a path in the base of a covering map and a chosen point of the fiber over its
initial value determine a unique lifted path. -/
-- Proof sketch: convert `hp` to a mathlib covering map using
-- `IsPathConnectedCoveringMap.isCoveringMap`. Use `IsCoveringMap.exists_path_lifts` for existence,
-- and compare any other lift with the canonical one via `IsCoveringMap.eq_liftPath_iff'`.
theorem existsUnique_pathLift (hp : IsPathConnectedCoveringMap p) (gamma : C(I, B)) (e : E)
    (h0 : gamma 0 = p e) :
    ∃! Gamma : C(I, E), p ∘ Gamma = gamma ∧ Gamma 0 = e := by
  refine ⟨hp.isCoveringMap.liftPath gamma e h0, ?_, ?_⟩
  · exact ⟨hp.isCoveringMap.liftPath_lifts gamma e h0, hp.isCoveringMap.liftPath_zero gamma e h0⟩
  · intro Gamma hGamma
    exact (hp.isCoveringMap.eq_liftPath_iff' h0).2 hGamma

end IsPathConnectedCoveringMap

/-! ### Theorem_3_2_2 (from Chap03) -/
open scoped unitInterval

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

namespace IsCoveringMap

variable {p : E → B}

/-- Theorem 3.2.2: homotopic paths in the base of a covering map starting at `b₀` lift to
homotopic paths in the total space relative to `{0, 1}` from a chosen point `e` over `b₀`. -/
-- Proof sketch: view `h : γ₀.Homotopic γ₁` as a homotopy relative `{0, 1}` of the underlying
-- continuous maps. Then apply `IsCoveringMap.homotopicRel_iff_comp` to the two lifted paths,
-- using `liftPath_zero` to witness that they agree at the initial point.
theorem liftPath_homotopicRel_of_homotopic (hp : IsCoveringMap p) {b₀ b₁ : B}
    {γ₀ γ₁ : Path b₀ b₁} (h : γ₀.Homotopic γ₁) (e : E) (he : p e = b₀) :
    (hp.liftPath γ₀ e (γ₀.source.trans he.symm)).HomotopicRel
      (hp.liftPath γ₁ e (γ₁.source.trans he.symm)) {0, 1} := by
  obtain ⟨H⟩ := h
  refine (hp.homotopicRel_iff_comp ?_).2 ?_
  · exact ⟨0, by simp, by simp [hp.liftPath_zero]⟩
  · convert (show (γ₀ : C(I, B)).HomotopicRel γ₁ {0, 1} from ⟨H⟩) using 1
    · ext t
      exact congr_fun (hp.liftPath_lifts γ₀ e (γ₀.source.trans he.symm)) t
    · ext t
      exact congr_fun (hp.liftPath_lifts γ₁ e (γ₁.source.trans he.symm)) t

/-- Homotopic base paths with the same chosen starting lift have the same lifted endpoint. -/
-- Proof sketch: apply `IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel` to the path homotopy
-- `h`, viewed as a homotopy relative `{0, 1}` of the underlying continuous maps.
theorem liftPath_apply_one_eq_of_homotopic (hp : IsCoveringMap p) {b₀ b₁ : B}
    {γ₀ γ₁ : Path b₀ b₁} (h : γ₀.Homotopic γ₁) (e : E) (he : p e = b₀) :
    hp.liftPath γ₀ e (γ₀.source.trans he.symm) 1 =
      hp.liftPath γ₁ e (γ₁.source.trans he.symm) 1 := by
  obtain ⟨H⟩ := h
  exact hp.liftPath_apply_one_eq_of_homotopicRel ⟨H⟩ e
    (γ₀.source.trans he.symm) (γ₁.source.trans he.symm)

end IsCoveringMap

/-! ### Theorem_3_2_3 (from Chap03) -/
universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

namespace IsCoveringMap

variable {p : E → B}

/-- Theorem 3.2.3: a covering map `p : E → B` induces an injective homomorphism
`p_* : π₁(E, e) → π₁(B, p e)` on fundamental groups. -/
-- Proof sketch: specialize `IsCoveringMap.injective_path_homotopic_map` to loops based at `e`.
theorem fundamentalGroup_map_injective (hp : IsCoveringMap p) (e : E) :
    Function.Injective (FundamentalGroup.map ⟨p, hp.continuous⟩ e) := by
  simpa using hp.injective_path_homotopic_map e e

end IsCoveringMap

/-! ### Theorem_3_2_4 (from Chap03) -/
universe u v

noncomputable section

open CategoryTheory FundamentalGroup Path.Homotopic.Quotient
open scoped FundamentalGroup Pointwise

namespace IsCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable {p : E → B}

private theorem fundamentalGroup_mapOfEq_comp_basepointChange (hp : IsCoveringMap p)
    {b : B} {e e' : p ⁻¹' {b}} (δ : Path e.1 e'.1) :
    (mapOfEq ⟨p, hp.continuous⟩ e'.property).comp (γ[δ]).toMonoidHom =
      (γ[((δ.map hp.continuous).cast e.property.symm e'.property.symm)]).toMonoidHom.comp
        (mapOfEq ⟨p, hp.continuous⟩ e.property) := by
  let he : p e.1 = b := e.property
  let he' : p e'.1 = b := e'.property
  let F := FundamentalGroupoid.map ⟨p, hp.continuous⟩
  let eδ : FundamentalGroupoid.mk e.1 ≅ FundamentalGroupoid.mk e'.1 :=
    (Groupoid.isoEquivHom _ _).symm ⟦δ⟧
  let eb : FundamentalGroupoid.mk (p e.1) ≅ FundamentalGroupoid.mk b :=
    eqToIso (congrArg FundamentalGroupoid.mk he)
  let eb' : FundamentalGroupoid.mk (p e'.1) ≅ FundamentalGroupoid.mk b :=
    eqToIso (congrArg FundamentalGroupoid.mk he')
  let eδb : FundamentalGroupoid.mk b ≅ FundamentalGroupoid.mk b :=
    (Groupoid.isoEquivHom _ _).symm ⟦(δ.map hp.continuous).cast he.symm he'.symm⟧
  have heδb :
      eδb = eb.symm ≪≫ F.mapIso eδ ≪≫ eb' := by
    ext
    simpa [eδb, eδ, eb, eb', F, mk_map] using
      (FundamentalGroupoid.conj_eqToHom he.symm he'.symm).symm
  ext α
  change eb'.conj (F.map (eδ.conj α)) = eδb.conj (eb.conj (F.map α))
  (convert congrArg eb'.conj (F.map_conj eδ α) using 1; simp [heδb])
  rfl

private theorem fundamentalGroup_map_range_conjugate_of_path (hp : IsCoveringMap p) {b : B}
    (e e' : p ⁻¹' {b}) (δ : Path e.1 e'.1) :
    ∃ g : FundamentalGroup B b,
      (mapOfEq ⟨p, hp.continuous⟩ e'.property).range =
        MulAut.conj g • (mapOfEq ⟨p, hp.continuous⟩ e.property).range := by
  let he : p e.1 = b := e.property
  let he' : p e'.1 = b := e'.property
  let g : FundamentalGroup B b := fromPath ⟦(δ.map hp.continuous).cast he.symm he'.symm⟧
  refine ⟨g, ?_⟩
  let m : FundamentalGroup E e.1 →* FundamentalGroup B b := mapOfEq ⟨p, hp.continuous⟩ he
  let m' : FundamentalGroup E e'.1 →* FundamentalGroup B b := mapOfEq ⟨p, hp.continuous⟩ he'
  let c : FundamentalGroup E e.1 →* FundamentalGroup E e'.1 := (γ[δ]).toMonoidHom
  have hcomp :
      m'.comp c =
        (γ[((δ.map hp.continuous).cast he.symm he'.symm)]).toMonoidHom.comp m :=
    fundamentalGroup_mapOfEq_comp_basepointChange hp δ
  have hcomp' : m'.comp c = (MulAut.conj g).toMonoidHom.comp m := by
    simpa [g] using hcomp
  have hrange : (m'.comp c).range = m'.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective c (γ[δ]).surjective,
      ← MonoidHom.range_eq_map]
  calc
    m'.range = (m'.comp c).range := hrange.symm
    _ = ((MulAut.conj g).toMonoidHom.comp m).range := by rw [hcomp']
    _ = m.range.map (MulAut.conj g).toMonoidHom := MonoidHom.range_comp _ _
    _ = MulAut.conj g • m.range := by
      rfl

/-- If two points in the fiber `p ⁻¹' {b}` are joined by a path in `E`, then the image subgroups
of the induced maps on fundamental groups at those points are conjugate inside `π₁(B, b)`. -/
-- Proof sketch: choose a path `δ` joining the two fiber points. The projected loop `(p ∘ δ)` at
-- `b` defines the conjugating element `g : π₁(B, b)`, and naturality of `mapOfEq` with respect to
-- basepoint change identifies the two image subgroups up to the inner automorphism `MulAut.conj g`.
theorem fundamentalGroup_map_range_conjugate (hp : IsCoveringMap p) {b : B}
    (e e' : p ⁻¹' {b}) (h : Joined e.1 e'.1) :
    ∃ g : FundamentalGroup B b,
      (mapOfEq ⟨p, hp.continuous⟩ e'.property).range =
        MulAut.conj g • (mapOfEq ⟨p, hp.continuous⟩ e.property).range :=
  fundamentalGroup_map_range_conjugate_of_path hp e e' h.somePath

/-- Theorem 3.2.4: if `E` is path connected and `e,e' : E` lie in the same fiber of a covering
map `p : E → B`, then the image subgroups of the induced maps on fundamental groups at `e` and
`e'` are conjugate inside `π₁(B, b)`. -/
theorem fundamentalGroup_map_range_conjugate_of_pathConnectedSpace [PathConnectedSpace E]
    (hp : IsCoveringMap p) {b : B} (e e' : p ⁻¹' {b}) :
    ∃ g : FundamentalGroup B b,
      (mapOfEq ⟨p, hp.continuous⟩ e'.property).range =
        MulAut.conj g • (mapOfEq ⟨p, hp.continuous⟩ e.property).range :=
  fundamentalGroup_map_range_conjugate hp e e' (PathConnectedSpace.joined e.1 e'.1)

end IsCoveringMap

/-! ### Theorem_3_2_5 (from Chap03) -/
noncomputable section

open CategoryTheory FundamentalGroup Path.Homotopic.Quotient
open scoped FundamentalGroup Pointwise

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

namespace IsCoveringMap

variable {p : E → B}

/-- Helper for Theorem 3.2.5: `mapOfEq` commutes with basepoint change along a path inside a
fiber of a covering map. -/
theorem mapOfEq_comp_basepoint_change (hp : IsCoveringMap p) {b : B} {e e' : p ⁻¹' {b}}
    (δ : Path e.1 e'.1) :
    (mapOfEq ⟨p, hp.continuous⟩ e'.property).comp (γ[δ]).toMonoidHom =
      (γ[((δ.map hp.continuous).cast e.property.symm e'.property.symm)]).toMonoidHom.comp
        (mapOfEq ⟨p, hp.continuous⟩ e.property) := by
  let he : p e.1 = b := e.property
  let he' : p e'.1 = b := e'.property
  let F := FundamentalGroupoid.map ⟨p, hp.continuous⟩
  let eδ : FundamentalGroupoid.mk e.1 ≅ FundamentalGroupoid.mk e'.1 :=
    (Groupoid.isoEquivHom _ _).symm ⟦δ⟧
  let eb : FundamentalGroupoid.mk (p e.1) ≅ FundamentalGroupoid.mk b :=
    eqToIso (congrArg FundamentalGroupoid.mk he)
  let eb' : FundamentalGroupoid.mk (p e'.1) ≅ FundamentalGroupoid.mk b :=
    eqToIso (congrArg FundamentalGroupoid.mk he')
  let eδb : FundamentalGroupoid.mk b ≅ FundamentalGroupoid.mk b :=
    (Groupoid.isoEquivHom _ _).symm ⟦(δ.map hp.continuous).cast he.symm he'.symm⟧
  -- Compare the two ways of transporting the projected path class back to the basepoint `b`.
  have heδb :
      eδb = eb.symm ≪≫ F.mapIso eδ ≪≫ eb' := by
    ext
    simpa [eδb, eδ, eb, eb', F, mk_map] using
      (FundamentalGroupoid.conj_eqToHom he.symm he'.symm).symm
  ext α
  -- Evaluate both monoid homomorphisms on a loop and use functoriality of conjugation.
  change eb'.conj (F.map (eδ.conj α)) = eδb.conj (eb.conj (F.map α))
  (convert congrArg eb'.conj (F.map_conj eδ α) using 1; simp [heδb])
  rfl

/-- Helper for Theorem 3.2.5: a path joining two points of the same fiber conjugates the image
subgroup of `π₁(E)` by the projected loop in the base. -/
theorem mapOfEq_range_conjugate_of_path (hp : IsCoveringMap p) {b : B}
    (e e' : p ⁻¹' {b}) (δ : Path e.1 e'.1) :
    (mapOfEq ⟨p, hp.continuous⟩ e'.property).range =
      MulAut.conj (fromPath ⟦(δ.map hp.continuous).cast e.property.symm e'.property.symm⟧) •
        (mapOfEq ⟨p, hp.continuous⟩ e.property).range := by
  let he : p e.1 = b := e.property
  let he' : p e'.1 = b := e'.property
  let g : FundamentalGroup B b := fromPath ⟦(δ.map hp.continuous).cast he.symm he'.symm⟧
  let m : FundamentalGroup E e.1 →* FundamentalGroup B b := mapOfEq ⟨p, hp.continuous⟩ he
  let m' : FundamentalGroup E e'.1 →* FundamentalGroup B b := mapOfEq ⟨p, hp.continuous⟩ he'
  let c : FundamentalGroup E e.1 →* FundamentalGroup E e'.1 := (γ[δ]).toMonoidHom
  -- Rewrite the naturality square from the previous helper into a conjugation statement.
  have hcomp :
      m'.comp c =
        (γ[((δ.map hp.continuous).cast he.symm he'.symm)]).toMonoidHom.comp m :=
    mapOfEq_comp_basepoint_change hp δ
  have hcomp' : m'.comp c = (MulAut.conj g).toMonoidHom.comp m := by
    simpa [g] using hcomp
  have hrange : (m'.comp c).range = m'.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective c (γ[δ]).surjective,
      ← MonoidHom.range_eq_map]
  calc
    m'.range = (m'.comp c).range := hrange.symm
    _ = ((MulAut.conj g).toMonoidHom.comp m).range := by rw [hcomp']
    _ = m.range.map (MulAut.conj g).toMonoidHom := MonoidHom.range_comp _ _
    _ = MulAut.conj g • m.range := by
      rfl

/-- Helper for Theorem 3.2.5: lifting a loop at `b` from a point in the fiber ends again in the
fiber over `b`. -/
theorem liftPath_endpoint_mem_fiber (hp : IsCoveringMap p) {b : B} (e : p ⁻¹' {b})
    (γ : Path b b) :
    p (hp.liftPath γ e.1 (γ.source.trans e.2.symm) 1) = b := by
  -- Project the lifted loop back to the base and evaluate at the endpoint.
  simpa using
    (congr_fun (hp.liftPath_lifts γ e.1 (γ.source.trans e.2.symm)) 1).trans γ.target

/-- Helper for Theorem 3.2.5: the endpoint of the lifted loop defines a new point of the fiber
over `b`. -/
abbrev lifted_loop_endpoint (hp : IsCoveringMap p) {b : B} (e : p ⁻¹' {b}) (γ : Path b b) :
    p ⁻¹' {b} :=
  ⟨hp.liftPath γ e.1 (γ.source.trans e.2.symm) 1, liftPath_endpoint_mem_fiber hp e γ⟩

/-- Helper for Theorem 3.2.5: the chosen lift of a loop at `b` is a path from `e` to the lifted
endpoint in the total space. -/
abbrev lifted_loop_path (hp : IsCoveringMap p) {b : B} (e : p ⁻¹' {b}) (γ : Path b b) :
    Path e.1 (lifted_loop_endpoint hp e γ).1 :=
  Path.mk (hp.liftPath γ e.1 (γ.source.trans e.2.symm))
    (hp.liftPath_zero γ e.1 (γ.source.trans e.2.symm))
    rfl

/-- Helper for Theorem 3.2.5: projecting the chosen lifted loop back to the base recovers the
original loop. -/
theorem liftPath_projection_eq_loop (hp : IsCoveringMap p) {b : B} (e : p ⁻¹' {b})
    (γ : Path b b) :
    ((lifted_loop_path hp e γ).map hp.continuous).cast e.property.symm
      (lifted_loop_endpoint hp e γ).property.symm = γ := by
  -- The lifted path was defined precisely so that its projection is `γ` pointwise.
  ext t
  simpa [lifted_loop_path] using
    congr_fun (hp.liftPath_lifts γ e.1 (γ.source.trans e.2.symm)) t

/-- Helper for Theorem 3.2.5: every concrete loop representative of a class in `π₁(B, b)` lifts
to a fiber point whose image subgroup is the corresponding conjugate. -/
theorem exists_fiberPoint_mapOfEq_range_eq_conjugate_of_loop (hp : IsCoveringMap p) {b : B}
    (e : p ⁻¹' {b}) (γ : Path b b) :
    ∃ e' : p ⁻¹' {b},
      (mapOfEq ⟨p, hp.continuous⟩ e'.property).range =
        MulAut.conj (fromPath ⟦γ⟧) • (mapOfEq ⟨p, hp.continuous⟩ e.property).range := by
  refine ⟨lifted_loop_endpoint hp e γ, ?_⟩
  have hconj :=
    mapOfEq_range_conjugate_of_path (hp := hp) e (lifted_loop_endpoint hp e γ)
      (lifted_loop_path hp e γ)
  -- Replace the projected lifted loop by the original loop representative `γ`.
  rwa [liftPath_projection_eq_loop (hp := hp) e γ] at hconj

/-- Theorem 3.2.5: every conjugate of the subgroup
`p_*(π₁(E, e)) ≤ π₁(B, b)` is realized as the image subgroup coming from some other point of the
fiber `p ⁻¹' {b}`. -/
-- Proof sketch: represent `g : π₁(B, b)` by a loop at `b`, lift that loop through `p` starting at
-- `e`, and let `e'` be the endpoint of the lifted loop. The lifted path gives the required
-- conjugacy relation between the two image subgroups.
theorem exists_fiberPoint_mapOfEq_range_eq_conjugate (hp : IsCoveringMap p) {b : B}
    (e : p ⁻¹' {b}) (g : FundamentalGroup B b) :
    ∃ e' : p ⁻¹' {b},
      (mapOfEq ⟨p, hp.continuous⟩ e'.property).range =
        MulAut.conj g • (mapOfEq ⟨p, hp.continuous⟩ e.property).range := by
  -- Choose a loop representative of `g`, lift it from `e`, and apply the loop-level lemma.
  simpa using
    (Path.Homotopic.Quotient.ind
      (motive := fun q : Path.Homotopic.Quotient b b ↦
        ∃ e' : p ⁻¹' {b},
          (mapOfEq ⟨p, hp.continuous⟩ e'.property).range =
            MulAut.conj (fromPath q) • (mapOfEq ⟨p, hp.continuous⟩ e.property).range)
      (fun γ ↦ exists_fiberPoint_mapOfEq_range_eq_conjugate_of_loop (hp := hp) e γ)
      (FundamentalGroup.toPath g))

end IsCoveringMap

/-! ### Definition_3_2_6 (from Chap03) -/
universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- Definition 3.2.6: a covering map `p : E → B` is regular, relative to a chosen basepoint
`e : E`, if `p` is a covering in the sense of Definition 3.1.5 and the image subgroup
`p_*(π₁(E,e)) ≤ π₁(B, p e)` is normal. -/
structure IsRegularCoveringMap (p : E → B) (e : E) : Prop
    extends toIsPathConnectedCoveringMap : IsPathConnectedCoveringMap p where
  /-- The image subgroup of the induced homomorphism on fundamental groups at `e` is normal in
  the fundamental group of the base at `p e`. -/
  normal_fundamentalGroup_map_range :
    ((FundamentalGroup.map
        ⟨p, (IsPathConnectedCoveringMap.isCoveringMap toIsPathConnectedCoveringMap).continuous⟩
        e).range).Normal

namespace IsRegularCoveringMap

variable {p : E → B} {e : E}

/-- A regular covering map is, in particular, a path-connected covering map. -/
theorem isPathConnectedCoveringMap (hp : IsRegularCoveringMap p e) :
    IsPathConnectedCoveringMap p :=
  hp.toIsPathConnectedCoveringMap

/-- A regular covering map is, in particular, a covering map. -/
theorem isCoveringMap (hp : IsRegularCoveringMap p e) : IsCoveringMap p :=
  hp.isPathConnectedCoveringMap.isCoveringMap

/-- A regular covering map is surjective. -/
theorem surjective (hp : IsRegularCoveringMap p e) : Function.Surjective p :=
  hp.isPathConnectedCoveringMap.surjective

/-- A regular covering map is, in particular, a path-connected covering map. -/
instance (hp : IsRegularCoveringMap p e) : IsPathConnectedCoveringMap p :=
  hp.isPathConnectedCoveringMap

end IsRegularCoveringMap

/-! ### Definition_3_2_7 (from Chap03) -/
universe u v

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]

/-- Definition 3.2.7: a covering map in the sense of Definition 3.1.5 is universal when its total
space `E` is simply connected. -/
def IsUniversalCoveringMap (p : E → X) : Prop :=
  IsPathConnectedCoveringMap p ∧ SimplyConnectedSpace E

namespace IsUniversalCoveringMap

variable {p : E → X}

/-- A universal covering map is, in particular, a covering map in the sense of Definition 3.1.5. -/
theorem isPathConnectedCoveringMap (hp : IsUniversalCoveringMap p) :
    IsPathConnectedCoveringMap p := hp.1

/-- A universal covering map is surjective. -/
theorem surjective (hp : IsUniversalCoveringMap p) : Function.Surjective p :=
  hp.1.surjective

/-- A universal covering map is, in particular, a covering map. -/
theorem isCoveringMap (hp : IsUniversalCoveringMap p) : IsCoveringMap p :=
  hp.1.isCoveringMap

/-- The total space of a universal covering map is simply connected. -/
theorem simplyConnectedSpace (hp : IsUniversalCoveringMap p) : SimplyConnectedSpace E := hp.2


end IsUniversalCoveringMap

/-! ### Example_3_2_8 (from Chap03) -/
noncomputable section

open scoped TopCat

/-- Internal direct-subtype model of `S^n` as the unit sphere in `ℝ^(n+1)`. -/
private abbrev SphereModel (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- Helper for Example 3.2.8: the ambient Euclidean space of the sphere model has the expected
finite dimension. -/
private instance sphereModel_finrank_fact (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨@finrank_euclideanSpace_fin ℝ _ (n + 1)⟩

/-- Helper for Example 3.2.8: the last coordinate unit vector lies on the concrete sphere model. -/
private theorem sphereModelNorthPole_mem (n : ℕ) :
    EuclideanSpace.single (Fin.last n) (1 : ℝ) ∈ SphereModel n := by
  -- The chosen vector has norm one, so it belongs to the unit sphere.
  simp [SphereModel]

/-- Helper for Example 3.2.8: a concrete basepoint on the sphere model. -/
private def sphereModelNorthPole (n : ℕ) : SphereModel n :=
  ⟨EuclideanSpace.single (Fin.last n) (1 : ℝ), sphereModelNorthPole_mem n⟩

/-- Helper for Example 3.2.8: the sphere model inherits local path connectedness from its manifold
charts. -/
private theorem sphereModel_locPathConnectedSpace
    (n : ℕ) : LocPathConnectedSpace (SphereModel n) := by
  -- The sphere carries the standard manifold structure with Euclidean model space.
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (SphereModel n) := inferInstance
  let _ : LocPathConnectedSpace (EuclideanSpace ℝ (Fin n)) := inferInstance
  exact ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin n)) (SphereModel n)

/-- The canonical sphere `S^n` is locally path connected. -/
theorem sphere_locPathConnectedSpace (n : ℕ) : LocPathConnectedSpace (𝕊 n) := by
  let _ : LocPathConnectedSpace (SphereModel n) := sphereModel_locPathConnectedSpace n
  exact Homeomorph.ulift.isOpenEmbedding.locPathConnectedSpace

instance (n : ℕ) : LocPathConnectedSpace (𝕊 n) :=
  sphere_locPathConnectedSpace n

/-- Helper for Example 3.2.8: `S^n` is path connected once `n ≥ 2`. -/
private theorem sphereModel_pathConnectedSpace_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    PathConnectedSpace (SphereModel n) := by
  -- Convert the dimension hypothesis into the rank hypothesis needed by `isPathConnected_sphere`.
  have hdim : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace]
    simp [Fintype.card_fin]
    omega
  have hs : IsPathConnected (SphereModel n) := by
    simpa [SphereModel] using
      (isPathConnected_sphere
        hdim
        (0 : EuclideanSpace ℝ (Fin (n + 1)))
        (by norm_num : 0 ≤ (1 : ℝ)))
  exact isPathConnected_iff_pathConnectedSpace.mp hs

/-- `S^n` is path connected once `n ≥ 2`. -/
theorem sphere_pathConnectedSpace_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    PathConnectedSpace (𝕊 n) := by
  let _ : PathConnectedSpace (SphereModel n) := sphereModel_pathConnectedSpace_of_two_le hn
  exact Homeomorph.ulift.symm.surjective.pathConnectedSpace Homeomorph.ulift.symm.continuous

instance (n : ℕ) : LocPathConnectedSpace (RealProjectiveSpace n) := by
  dsimp [RealProjectiveSpace]
  infer_instance

/-- Helper for Example 3.2.8: a punctured sphere chart identifies the complement of one point
with Euclidean space. -/
private def sphereModel_punctured_homeomorph_euclidean (n : ℕ) (v : SphereModel n) :
    ({v}ᶜ : Set (SphereModel n)) ≃ₜ EuclideanSpace ℝ (Fin n) := by
  -- Rewrite the source and target of `stereographic'` into the concrete punctured-sphere chart.
  let e : ({v}ᶜ : Set (SphereModel n)) ≃ₜ
      (Set.univ : Set (EuclideanSpace ℝ (Fin n))) := by
    have hsource : (stereographic' n v).source = {v}ᶜ := stereographic'_source v
    have htarget : (stereographic' n v).target = Set.univ := stereographic'_target v
    rw [← hsource, ← htarget]
    exact (stereographic' n v).toHomeomorphSourceTarget
  exact e.trans (Homeomorph.Set.univ _)

/-- Helper for Example 3.2.8: every punctured sphere chart is contractible because it is
homeomorphic to Euclidean space. -/
private theorem sphereModel_punctured_contractible (n : ℕ) (v : SphereModel n) :
    ContractibleSpace ({v}ᶜ : Set (SphereModel n)) := by
  -- Transport contractibility across the stereographic homeomorphism.
  exact (sphereModel_punctured_homeomorph_euclidean n v).contractibleSpace

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Example 3.2.8: the stereographic chart with pole `v` sends the antipode `-v` to
the origin. -/
private theorem sphereModel_stereographic_antipode_eq_zero (n : ℕ) (v : SphereModel n) :
    stereographic' n v (-v) = 0 := by
  -- This is the standard stereographic-projection normalization at the opposite pole.
  have h : stereographic' n (-(-v)) (-v) = 0 := by
    dsimp [stereographic']
    simp only [EmbeddingLike.map_eq_zero_iff]
    exact stereographic_neg_apply (-v)
  simpa using h

/-- Helper for Example 3.2.8: removing a point and its antipode from the sphere model gives a
space homeomorphic to punctured Euclidean space. -/
private def sphereModel_doublePunctured_homeomorph_punctured_euclidean
    (n : ℕ) (v : SphereModel n) :
    ({v}ᶜ ∩ {-v}ᶜ : Set (SphereModel n)) ≃ₜ
      ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := by
  let e := stereographic' n v
  have hs :
      ({v}ᶜ ∩ {-v}ᶜ : Set (SphereModel n)) ⊆ e.source := by
    -- The double-punctured set is contained in the source complement `{v}ᶜ`.
    intro x hx
    rw [stereographic'_source]
    exact hx.1
  have himage :
      e '' ({v}ᶜ ∩ {-v}ᶜ : Set (SphereModel n)) =
        ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hzero
      have hvsource : (-v : SphereModel n) ∈ e.source := by
        rw [stereographic'_source]
        simpa [eq_comm] using (ne_neg_of_mem_unit_sphere ℝ v)
      have hxeq : x = -v := by
        have hxsource : x ∈ e.source := by
          rw [stereographic'_source]
          exact hx.1
        calc
          x = e.symm (e x) := by
            exact (e.left_inv hxsource).symm
          _ = e.symm 0 := by rw [hzero]
          _ = -v := by
            rw [← sphereModel_stereographic_antipode_eq_zero n v]
            exact e.left_inv hvsource
      exact hx.2 hxeq
    · rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hy
      have hytarget : y ∈ e.target := by
        rw [stereographic'_target]
        simp
      have hsrc : e.symm y ∈ e.source := e.map_target hytarget
      have hneq_v : e.symm y ≠ v := by
        rw [stereographic'_source] at hsrc
        exact hsrc
      have hmap : e (e.symm y) = y := e.right_inv hytarget
      refine ⟨e.symm y, ⟨hneq_v, ?_⟩, hmap⟩
      intro hxneg
      have hyzero : y = 0 := by
        calc
          y = e (e.symm y) := hmap.symm
          _ = e (-v) := by rw [hxneg]
          _ = 0 := sphereModel_stereographic_antipode_eq_zero n v
      exact hy hyzero
  -- Restrict the stereographic chart to the complement of the antipode.
  exact e.homeomorphOfImageSubsetSource hs himage

/-- Helper for Example 3.2.8: the overlap of the two antipodal puncture charts is path connected
as soon as `n ≥ 2`. -/
private theorem sphereModel_overlap_pathConnected_of_two_le {n : ℕ} (hn : 2 ≤ n)
    (v : SphereModel n) :
    PathConnectedSpace ({v}ᶜ ∩ {-v}ᶜ : Set (SphereModel n)) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
    -- The Euclidean chart has dimension `n`, and `n ≥ 2` gives the rank bound.
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace]
    have hnat : 1 < n := by
      omega
    simpa using hnat
  have htarget :
      IsPathConnected ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ :
        Set (EuclideanSpace ℝ (Fin n))) :=
    isPathConnected_compl_singleton_of_one_lt_rank hrank 0
  let _ :
      PathConnectedSpace ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ :
        Set (EuclideanSpace ℝ (Fin n))) :=
    isPathConnected_iff_pathConnectedSpace.mp htarget
  let h :=
    sphereModel_doublePunctured_homeomorph_punctured_euclidean n v
  have hdomain :
      IsPathConnected ({v}ᶜ ∩ {-v}ᶜ : Set (SphereModel n)) := by
    -- Push forward the punctured Euclidean connectedness through the restricted chart.
    let f :
        ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ : Set (EuclideanSpace ℝ (Fin n))) →
          SphereModel n :=
      fun y ↦ (h.symm y : ({v}ᶜ ∩ {-v}ᶜ : Set (SphereModel n)))
    have hf : Continuous f := continuous_subtype_val.comp h.symm.continuous
    have himage :
        f '' (Set.univ :
          Set ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ : Set (EuclideanSpace ℝ (Fin n)))) =
          ({v}ᶜ ∩ {-v}ᶜ : Set (SphereModel n)) := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact (h.symm y).2
      · intro hx
        refine ⟨h ⟨x, hx⟩, Set.mem_univ _, ?_⟩
        simp [f]
    have himage_path :
        IsPathConnected
          (f '' (Set.univ :
            Set ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ :
              Set (EuclideanSpace ℝ (Fin n))))) :=
      isPathConnected_univ.image hf
    rw [himage] at himage_path
    exact himage_path
  exact isPathConnected_iff_pathConnectedSpace.mp hdomain

/-- Helper for Example 3.2.8: the concrete sphere model of `S^n` is simply connected for `n ≥ 2`.
-/
private theorem sphereModel_simplyConnected_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    SimplyConnectedSpace (SphereModel n) := by
  -- Route correction: replace the missing global sphere theorem by the two-chart van Kampen proof.
  let v : SphereModel n := sphereModelNorthPole n
  let U : TopologicalSpace.Opens (TopCat.of (SphereModel n)) := ⟨{v}ᶜ, isOpen_compl_singleton⟩
  let V : TopologicalSpace.Opens (TopCat.of (SphereModel n)) := ⟨{-v}ᶜ, isOpen_compl_singleton⟩
  have hU : ContractibleSpace U := by
    -- Each punctured chart is Euclidean, hence contractible.
    simpa [U] using sphereModel_punctured_contractible n v
  have hV : ContractibleSpace V := by
    -- The same contractibility argument applies to the opposite puncture chart.
    simpa [V] using sphereModel_punctured_contractible n (-v)
  let _ : ContractibleSpace U := hU
  let _ : ContractibleSpace V := hV
  let _ : PathConnectedSpace U := by infer_instance
  let _ : SimplyConnectedSpace V := by infer_instance
  let _ : PathConnectedSpace ↥(U ⊓ V) := by
    -- The overlap is punctured Euclidean space, so it stays path connected for `n ≥ 2`.
    simpa [U, V, TopologicalSpace.Opens.coe_inf] using
      sphereModel_overlap_pathConnected_of_two_le hn v
  let _ : PathConnectedSpace (SphereModel n) := sphereModel_pathConnectedSpace_of_two_le hn
  have hcover : U ⊔ V = ⊤ := by
    -- No sphere point can equal both `v` and `-v`, so the two puncture complements cover.
    ext x
    constructor
    · intro _
      simp
    · intro _
      by_cases hx : x = v
      · right
        simpa [hx, eq_comm] using (ne_neg_of_mem_unit_sphere ℝ v)
      · left
        exact hx
  let x : ↥(U ⊓ V) := Classical.choice (PathConnectedSpace.nonempty : Nonempty ↥(U ⊓ V))
  have hsurj :
      Function.Surjective (FundamentalGroup.map (TopologicalSpace.Opens.inclusion' U).hom
        ⟨x.1, x.2.1⟩) :=
    fundamental_group_left_to_union_surjective U V hcover x.1 x.2.1 x.2.2
  have hsub_U :
      Subsingleton (FundamentalGroup U ⟨x.1, x.2.1⟩) := by
    -- Contractibility of the left chart trivializes its based fundamental group.
    let xU : U := ⟨x.1, x.2.1⟩
    change Subsingleton (Path.Homotopic.Quotient xU xU)
    infer_instance
  have hsub_base : Subsingleton (FundamentalGroup (SphereModel n) x.1) := by
    -- Surjectivity from the contractible chart forces the ambient based loop group to be trivial.
    refine ⟨fun γ δ ↦ ?_⟩
    rcases hsurj γ with ⟨γU, rfl⟩
    rcases hsurj δ with ⟨δU, rfl⟩
    exact congrArg
      (FundamentalGroup.map (TopologicalSpace.Opens.inclusion' U).hom ⟨x.1, x.2.1⟩)
      (@Subsingleton.elim _ hsub_U γU δU)
  have hsub_all : ∀ y : SphereModel n, Subsingleton (FundamentalGroup (SphereModel n) y) :=
    fun y ↦ by
      let e : FundamentalGroup (SphereModel n) x.1 ≃* FundamentalGroup (SphereModel n) y :=
        FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x.1 y
      let _ : Subsingleton (FundamentalGroup (SphereModel n) x.1) := hsub_base
      refine ⟨fun γ δ ↦ ?_⟩
      have hpre : e.symm γ = e.symm δ := Subsingleton.elim _ _
      simpa using congrArg e hpre
  -- Convert triviality of every based loop group into null-homotopy of every loop.
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, ?_⟩
  intro y γ
  let _ : Subsingleton (FundamentalGroup (SphereModel n) y) := hsub_all y
  have h :
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) :
        FundamentalGroup (SphereModel n) y) = 1 := by
    exact Subsingleton.elim _ _
  rw [show (1 : FundamentalGroup (SphereModel n) y) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (Path.refl y)) by rfl] at h
  exact Path.Homotopic.Quotient.eq.mp h

/-- `S^n` is simply connected for `n ≥ 2`. -/
theorem sphere_simplyConnected_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    SimplyConnectedSpace (𝕊 n) := by
  let _ : SimplyConnectedSpace (SphereModel n) := sphereModel_simplyConnected_of_two_le hn
  exact Homeomorph.ulift.toHomotopyEquiv.simplyConnectedSpace

/-- Example 3.2.8: for `n ≥ 2`, the antipodal quotient map from `S^n` to `RP^n` is a universal
covering map. -/
-- Proof sketch: upgrade the antipodal quotient map to a covering map in the sense of Definition
-- 3.1.5 by combining quotient surjectivity with path-connected evenly covered neighborhoods, then
-- use the standard fact that `S^n` is simply connected for `n ≥ 2`.
theorem sphereToRealProjectiveSpace_isUniversalCoveringMap {n : ℕ} (hn : 2 ≤ n) :
    IsUniversalCoveringMap (sphereToRealProjectiveSpace n) := by
  have _ : PathConnectedSpace ↥(TopCat.sphere.{0} n) := by
    simpa using sphere_pathConnectedSpace_of_two_le hn
  refine ⟨?_, sphere_simplyConnected_of_two_le hn⟩
  -- Upgrade the covering-map statement to the textbook path-connected version.
  exact
    IsCoveringMap.isPathConnectedCoveringMap
      (sphereToRealProjectiveSpace_isCoveringMap n)
      (by
        simpa [sphereToRealProjectiveSpace] using
          (Quotient.mk''_surjective :
            Function.Surjective
              (Quotient.mk'' : 𝕊 n → RealProjectiveSpace n)))

/-! ### Corollary_3_2_9 (from Chap03) -/
open scoped FundamentalGroup TopCat

noncomputable section

/-- Helper for Corollary 3.2.9: after projecting a lifted loop and casting its endpoint back to the
basepoint, one recovers the original loop. -/
private theorem liftPath_projection_eq_loop
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
    (hp : IsCoveringMap p) (e : E) (γ : Path (p e) (p e)) {y : E}
    (hy : y = hp.liftPath γ e γ.source 1) (hb : p y = p e) :
    (((Path.mk (hp.liftPath γ e γ.source) (hp.liftPath_zero γ e γ.source) rfl).cast rfl hy).map
      hp.continuous).cast rfl hb.symm = γ := by
  -- The lifted path was defined so that its projection agrees pointwise with `γ`.
  ext t
  simp only [ContinuousMap.toFun_eq_coe, Path.cast_coe, Path.map_coe, Path.coe_mk',
    Function.comp_apply]
  exact congr_fun (hp.liftPath_lifts γ e γ.source) t

/-- Helper for Corollary 3.2.9: the monodromy orbit map of a universal cover is injective. -/
private theorem universal_cover_fundamentalGroupToFiber_injective
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
    (hp : IsUniversalCoveringMap p) (e : E) :
    Function.Injective (fun γ : FundamentalGroup B (p e) ↦ hp.isCoveringMap.monodromy γ.toPath
      ⟨e, rfl⟩) := by
  let _ : SimplyConnectedSpace E := hp.simplyConnectedSpace
  change Function.Injective
    (fun γ : Path.Homotopic.Quotient (p e) (p e) ↦ hp.isCoveringMap.monodromy γ ⟨e, rfl⟩)
  intro γ₀ γ₁ hγ
  revert hγ
  refine Quotient.inductionOn₂ γ₀ γ₁ ?_
  intro γ₀' γ₁' hγ'
  let y : E := hp.isCoveringMap.liftPath γ₀' e γ₀'.source 1
  have hend :
      y = hp.isCoveringMap.liftPath γ₁' e γ₁'.source 1 := by
    -- Equality in the fiber says the two lifted loops have the same endpoint.
    exact congrArg Subtype.val hγ'
  have hb : p y = p e := by
    simpa using hp.isCoveringMap.liftPath_endpoint_mem_fiber ⟨e, rfl⟩ γ₀'
  let Γ₀ : Path e y :=
    Path.mk (hp.isCoveringMap.liftPath γ₀' e γ₀'.source)
      (hp.isCoveringMap.liftPath_zero γ₀' e γ₀'.source) rfl
  let Γ₁ : Path e y :=
    (Path.mk (hp.isCoveringMap.liftPath γ₁' e γ₁'.source)
      (hp.isCoveringMap.liftPath_zero γ₁' e γ₁'.source) rfl).cast rfl hend
  have hΓ :
      Path.Homotopic.Quotient.mk Γ₀ = Path.Homotopic.Quotient.mk Γ₁ := by
    -- Simply connectedness makes any two paths with these common endpoints homotopic.
    exact Path.Homotopic.Quotient.eq.mpr (SimplyConnectedSpace.paths_homotopic Γ₀ Γ₁)
  have hmap :
      (Path.Homotopic.Quotient.mk Γ₀).map ⟨p, hp.isCoveringMap.continuous⟩ =
        (Path.Homotopic.Quotient.mk Γ₁).map ⟨p, hp.isCoveringMap.continuous⟩ := by
    exact congrArg (fun q : Path.Homotopic.Quotient e y ↦ q.map ⟨p, hp.isCoveringMap.continuous⟩) hΓ
  have hmap_cast :
      ((Path.Homotopic.Quotient.mk Γ₀).map ⟨p, hp.isCoveringMap.continuous⟩).cast rfl hb.symm =
        ((Path.Homotopic.Quotient.mk Γ₁).map ⟨p, hp.isCoveringMap.continuous⟩).cast rfl
          hb.symm := by
    -- Cast both projected paths to actual loops at `p e`.
    exact congrArg (fun q : Path.Homotopic.Quotient (p e) (p y) ↦ q.cast rfl hb.symm) hmap
  have hγ₀ :
      ((Path.Homotopic.Quotient.mk Γ₀).map ⟨p, hp.isCoveringMap.continuous⟩).cast rfl hb.symm =
        Path.Homotopic.Quotient.mk γ₀' := by
    -- The first projected lift is the original loop `γ₀'`.
    exact congrArg Path.Homotopic.Quotient.mk
      (liftPath_projection_eq_loop hp.isCoveringMap e γ₀' rfl hb)
  have hγ₁ :
      ((Path.Homotopic.Quotient.mk Γ₁).map ⟨p, hp.isCoveringMap.continuous⟩).cast rfl hb.symm =
        Path.Homotopic.Quotient.mk γ₁' := by
    -- The same projection identity holds for the second lifted loop after endpoint alignment.
    exact congrArg Path.Homotopic.Quotient.mk
      (liftPath_projection_eq_loop hp.isCoveringMap e γ₁' hend hb)
  exact hγ₀.symm.trans (hmap_cast.trans hγ₁)

/-- Helper for Corollary 3.2.9: monodromy along the projected class of a path from `e` to `z`
recovers `z`. -/
private theorem universal_cover_fundamentalGroupToFiber_from_path
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
    (hp : IsUniversalCoveringMap p) {e z : E} (γ : Path e z) (hz : p z = p e) :
    hp.isCoveringMap.monodromy
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk ((γ.map hp.isCoveringMap.continuous).cast rfl hz.symm))).toPath
      ⟨e, rfl⟩ =
      ⟨z, hz⟩ := by
  have hγ :
      hp.isCoveringMap.liftPath ((γ.map hp.isCoveringMap.continuous).cast rfl hz.symm) e
          ((γ.map hp.isCoveringMap.continuous).cast rfl hz.symm).source =
        γ.toContinuousMap := by
    -- The original path `γ` is already the unique lift of its projected loop starting at `e`.
    refine
      ((hp.isCoveringMap.eq_liftPath_iff'
        ((γ.map hp.isCoveringMap.continuous).cast rfl hz.symm).source).2 ?_).symm
    constructor
    · ext t
      simp [Path.cast]
    · exact γ.source
  apply Subtype.ext
  -- Evaluating the uniqueness identity at `1` recovers the endpoint `z`.
  simpa using congrArg (fun f : C(↑unitInterval, E) ↦ f 1) hγ

/-- Helper for Corollary 3.2.9: the monodromy orbit map of a universal cover is surjective onto
the fiber over the chosen basepoint. -/
private theorem universal_cover_fundamentalGroupToFiber_surjective
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
    (hp : IsUniversalCoveringMap p) (e : E) :
    Function.Surjective (fun γ : FundamentalGroup B (p e) ↦ hp.isCoveringMap.monodromy γ.toPath
      ⟨e, rfl⟩) := by
  let _ : SimplyConnectedSpace E := hp.simplyConnectedSpace
  let _ : PathConnectedSpace E := inferInstance
  rintro ⟨z, hz⟩
  have hz' : p z = p e := by
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hz
  let γ : Path e z := PathConnectedSpace.somePath e z
  refine ⟨FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk ((γ.map hp.isCoveringMap.continuous).cast rfl hz'.symm)), ?_⟩
  -- Projecting a path from `e` to `z` gives a loop whose lifted endpoint is exactly `z`.
  simpa [γ] using universal_cover_fundamentalGroupToFiber_from_path hp γ hz'

/-- Helper for Corollary 3.2.9: a universal cover identifies `π₁(B, p e)` with the fiber over
`p e` by the monodromy orbit map based at `e`. -/
private noncomputable def universal_cover_fundamentalGroupFiberEquiv
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
    (hp : IsUniversalCoveringMap p) (e : E) :
    FundamentalGroup B (p e) ≃ p ⁻¹' {p e} :=
  Equiv.ofBijective
    (fun γ : FundamentalGroup B (p e) ↦ hp.isCoveringMap.monodromy γ.toPath ⟨e, rfl⟩)
    ⟨universal_cover_fundamentalGroupToFiber_injective hp e,
      universal_cover_fundamentalGroupToFiber_surjective hp e⟩

/-- Helper for Corollary 3.2.9: antipodal points define the same point of projective space. -/
private theorem sphereToRealProjectiveSpace_neg_eq (n : ℕ) (y : 𝕊 n) :
    sphereToRealProjectiveSpace n (-y) = sphereToRealProjectiveSpace n y := by
  -- The quotient relation identifies each point with its antipode.
  exact (sphereToRealProjectiveSpace_eq_iff n).2 (Or.inr rfl)

/-- Helper for Corollary 3.2.9: a point in the fiber over `sphereToRealProjectiveSpace n y` is
either `y` or `-y`. -/
private theorem sphereToRealProjectiveSpace_fiber_cases
    (n : ℕ) {y z : 𝕊 n}
    (hz : sphereToRealProjectiveSpace n z = sphereToRealProjectiveSpace n y) :
    z = y ∨ z = -y := by
  -- Equality in the quotient is exactly the antipodal relation.
  exact (sphereToRealProjectiveSpace_eq_iff n).1 hz

/-- Helper for Corollary 3.2.9: unpacking a point of the fiber gives an equality of projective
classes. -/
private theorem sphereToRealProjectiveSpace_eq_of_mem_fiber
    (n : ℕ) {y : 𝕊 n}
    (z : (sphereToRealProjectiveSpace n) ⁻¹' {sphereToRealProjectiveSpace n y}) :
    sphereToRealProjectiveSpace n z.1 = sphereToRealProjectiveSpace n y := by
  -- Membership in the singleton fiber is exactly equality of quotient points.
  exact z.2

/-- Helper for Corollary 3.2.9: the class of `y` itself belongs to the fiber over its projective
image. -/
private theorem sphereToRealProjectiveSpace_self_mem_fiber
    (n : ℕ) (y : 𝕊 n) :
    y ∈ (sphereToRealProjectiveSpace n) ⁻¹' {sphereToRealProjectiveSpace n y} := by
  -- The quotient map obviously sends `y` to its own class.
  simp [Set.mem_preimage, Set.mem_singleton_iff]

/-- Helper for Corollary 3.2.9: the antipode of `y` lies in the fiber over the class of `y`. -/
private theorem sphereToRealProjectiveSpace_neg_mem_fiber
    (n : ℕ) (y : 𝕊 n) :
    -y ∈ (sphereToRealProjectiveSpace n) ⁻¹' {sphereToRealProjectiveSpace n y} := by
  -- The quotient map sends antipodal points to the same projective point.
  simp [Set.mem_preimage, Set.mem_singleton_iff, sphereToRealProjectiveSpace_neg_eq]

/-- Helper for Corollary 3.2.9: distinguish the two points in a projective-space fiber by testing
whether the representative is literally `y`. -/
private def sphereToRealProjectiveSpace_fiber_toBool
    (n : ℕ) (y : 𝕊 n) :
    ((sphereToRealProjectiveSpace n) ⁻¹' {sphereToRealProjectiveSpace n y}) → Bool :=
  let _ := Classical.decEq (𝕊 n)
  fun z ↦ if z.1 = y then false else true

/-- Helper for Corollary 3.2.9: realize the two Boolean values by the two representatives `y` and
`-y` of the projective-space fiber. -/
private def bool_to_sphereToRealProjectiveSpace_fiber
    (n : ℕ) (y : 𝕊 n) :
    Bool → ((sphereToRealProjectiveSpace n) ⁻¹' {sphereToRealProjectiveSpace n y}) :=
  fun b ↦ if b then ⟨-y, sphereToRealProjectiveSpace_neg_mem_fiber n y⟩
    else ⟨y, sphereToRealProjectiveSpace_self_mem_fiber n y⟩

/-- Helper for Corollary 3.2.9: the Boolean-to-fiber map is a left inverse to the fiber
classification map. -/
private theorem sphereToRealProjectiveSpace_fiber_leftInverse
    (n : ℕ) (y : 𝕊 n) :
    Function.LeftInverse (bool_to_sphereToRealProjectiveSpace_fiber n y)
      (sphereToRealProjectiveSpace_fiber_toBool n y) := by
  classical
  intro z
  by_cases hz : z.1 = y
  · -- The `false` branch recovers the representative `y`.
    apply Subtype.ext
    simp [bool_to_sphereToRealProjectiveSpace_fiber, sphereToRealProjectiveSpace_fiber_toBool, hz]
  · have hz' : z.1 = -y := by
      rcases sphereToRealProjectiveSpace_fiber_cases n
          (sphereToRealProjectiveSpace_eq_of_mem_fiber n z) with hzy | hzy
      · exact (hz hzy).elim
      · exact hzy
    -- If the representative is not `y`, the fiber condition forces it to be `-y`.
    have hneq : (-y : 𝕊 n) ≠ y := sphere_neg_ne_self n y
    apply Subtype.ext
    simp [bool_to_sphereToRealProjectiveSpace_fiber, sphereToRealProjectiveSpace_fiber_toBool,
      hz', hneq]

/-- Helper for Corollary 3.2.9: the Boolean-to-fiber map is a right inverse to the fiber
classification map. -/
private theorem sphereToRealProjectiveSpace_fiber_rightInverse
    (n : ℕ) (y : 𝕊 n) :
    Function.RightInverse (bool_to_sphereToRealProjectiveSpace_fiber n y)
      (sphereToRealProjectiveSpace_fiber_toBool n y) := by
  classical
  intro b
  cases b
  · -- The `false` branch is represented by the chosen point `y`.
    change sphereToRealProjectiveSpace_fiber_toBool n y
        ⟨y, sphereToRealProjectiveSpace_self_mem_fiber n y⟩ = false
    simp [sphereToRealProjectiveSpace_fiber_toBool]
  · -- The `true` branch is represented by the antipode `-y`, which is distinct from `y`.
    change sphereToRealProjectiveSpace_fiber_toBool n y
        ⟨-y, sphereToRealProjectiveSpace_neg_mem_fiber n y⟩ = true
    simp [sphereToRealProjectiveSpace_fiber_toBool, sphere_neg_ne_self]

/-- Helper for Corollary 3.2.9: the geometric fiber of `S^n → RP^n` over the class of `y`
is a two-element type. -/
private theorem sphereToRealProjectiveSpace_fiber_toBool_bijective
    (n : ℕ) (y : 𝕊 n) :
    Function.Bijective (sphereToRealProjectiveSpace_fiber_toBool n y) := by
  refine ⟨(sphereToRealProjectiveSpace_fiber_leftInverse n y).injective,
    (sphereToRealProjectiveSpace_fiber_rightInverse n y).surjective⟩

/-- Helper for Corollary 3.2.9: the fiber of `S^n → RP^n` over the class of `y` has exactly two
elements, represented by `y` and `-y`. -/
private noncomputable def sphereToRealProjectiveSpace_fiber_equiv_bool
    (n : ℕ) (y : 𝕊 n) :
    ((sphereToRealProjectiveSpace n) ⁻¹' {sphereToRealProjectiveSpace n y}) ≃ Bool :=
  Equiv.ofBijective (sphereToRealProjectiveSpace_fiber_toBool n y)
    (sphereToRealProjectiveSpace_fiber_toBool_bijective n y)

/-- Helper for Corollary 3.2.9: the based fundamental group of `RP^n` has cardinality two once
`n ≥ 2`. -/
private theorem realProjectiveSpace_fundamentalGroup_card_two
    {n : ℕ} (hn : 2 ≤ n) (y : 𝕊 n) :
    Nat.card (FundamentalGroup (RealProjectiveSpace n) (sphereToRealProjectiveSpace n y)) = 2 := by
  -- Route correction: use the canonical universal cover from Example 3.2.8 instead of the local
  -- duplicate orbit-map wrapper that originally sat in this file.
  let hEquiv :=
    universal_cover_fundamentalGroupFiberEquiv
      (sphereToRealProjectiveSpace_isUniversalCoveringMap hn) y
  calc
    Nat.card (FundamentalGroup (RealProjectiveSpace n) (sphereToRealProjectiveSpace n y)) =
        Nat.card (((sphereToRealProjectiveSpace n) ⁻¹'
          {sphereToRealProjectiveSpace n y})) := by
      exact Nat.card_congr hEquiv
    _ = Nat.card Bool := by
      exact Nat.card_congr (sphereToRealProjectiveSpace_fiber_equiv_bool n y)
    _ = 2 := by
      simp

/-- Corollary 3.2.9: for `n ≥ 2`, the fundamental group of `RP^n` at any basepoint is the cyclic
group of order two. -/
theorem realProjectiveSpace_fundamentalGroup_mulEquiv_zmod_two {n : ℕ} (hn : 2 ≤ n)
    (x : RealProjectiveSpace n) :
    Nonempty (FundamentalGroup (RealProjectiveSpace n) x ≃* Multiplicative (ZMod 2)) := by
  rcases Quotient.exists_rep x with ⟨y, rfl⟩
  -- Represent the basepoint by `y`, compute the cardinality of `π₁`, and invoke the prime-card
  -- classification of groups of order two.
  refine ⟨mulEquivOfPrimeCardEq (realProjectiveSpace_fundamentalGroup_card_two hn y) ?_⟩
  simp
