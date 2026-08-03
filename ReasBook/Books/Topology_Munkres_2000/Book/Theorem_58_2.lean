module

public import Topology_Munkres_2000.Book.Exercise_55_5.Inclusion
public import Topology_Munkres_2000.Book.Lemma_58_1
public import Topology_Munkres_2000.Book.Notation_52_3.InducedMap
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

public section

universe u v

namespace FundamentalGroup.LeftToRight

/-- Helper for Theorem 58.2: pointed fundamental-group maps preserve composition,
including the endpoint equalities selecting their basepoints. -/
private theorem mapOfEq_comp {X : Type u} {Y : Type v} {Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) {x : X} {y : Y} {z : Z}
    (hf : f x = y) (hg : g y = z) (hgf : (g.comp f) x = z) :
    (mapOfEq g hg).comp (mapOfEq f hf) = mapOfEq (g.comp f) hgf := by
  -- Normalize the chosen endpoints before applying functoriality of mapped loops.
  subst y
  subst z
  have hg_rfl : hg = rfl := Subsingleton.elim _ _
  cases hg_rfl
  ext p
  simp only [MonoidHom.coe_comp, Function.comp_apply, mapOfEq_apply,
    MulOpposite.unop_op,
    Path.Homotopic.Quotient.cast_rfl_rfl, Path.Homotopic.Quotient.map_comp]
  exact congrArg MulOpposite.op (eq_of_heq (Path.Homotopic.Quotient.cast_heq _ _))

/-- Helper for Theorem 58.2: a reflexive endpoint choice in `mapOfEq` is the
ordinary induced map on fundamental groups. -/
private theorem mapOfEq_refl (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    mapOfEq f (rfl : f x = f x) = map f x := by
  -- Evaluate on loop classes and eliminate the reflexive endpoint casts.
  ext p
  simp only [mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl, map_apply,
    FundamentalGroup.map_apply]

/-- Helper for Theorem 58.2: the pointed fundamental-group map of the identity
continuous map is the identity homomorphism. -/
private theorem mapOfEq_id (X : Type u) [TopologicalSpace X] (x : X) :
    mapOfEq (ContinuousMap.id X) rfl = MonoidHom.id (π₁(X, x)) := by
  -- Evaluate on a representative loop class; identity mapping and reflexive casts disappear.
  ext p
  simp only [mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
  rcases p with ⟨⟨p⟩⟩
  rfl

/-- Helper for Theorem 58.2: equal continuous maps give equal pointed
fundamental-group maps, independently of their endpoint proofs. -/
private theorem mapOfEq_congr {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f g : C(X, Y))
    {x : X} {y : Y} (hfg : f = g) (hf : f x = y) (hg : g x = y) :
    mapOfEq f hf = mapOfEq g hg := by
  -- Substitute the map equality and use proof irrelevance for the endpoint witnesses.
  subst g
  congr

/-- Helper for Theorem 58.2: a strict retraction together with a homotopy relative
to the image basepoint makes the induced fundamental-group map bijective. -/
private theorem map_bijective_of_retractionHomotopicRel
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(Y, X)) (x : X)
    (hgf : g.comp f = ContinuousMap.id X)
    (H : (ContinuousMap.id Y).HomotopicRel (f.comp g) {f x}) :
    Function.Bijective (map f x) := by
  -- Evaluate the strict retraction law at the chosen basepoint to type the inverse map.
  have hgfx : g (f x) = x := by
    exact DFunLike.congr_fun hgf x
  let inverse := mapOfEq g hgfx
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨inverse, ?_, ?_⟩
  · -- The retraction equation makes the inverse a left inverse on loop classes.
    intro p
    have hgfAt : (g.comp f) x = x := hgfx
    have hleft : inverse.comp (map f x) = MonoidHom.id (π₁(X, x)) := by
      have hIdentity : mapOfEq (ContinuousMap.id X) rfl =
          MonoidHom.id (π₁(X, x)) := mapOfEq_id X x
      have hComposite : inverse.comp (map f x) =
          mapOfEq (ContinuousMap.id X) rfl := by
        calc
          inverse.comp (map f x) = inverse.comp (mapOfEq f rfl) := by
            rw [mapOfEq_refl]
          _ = mapOfEq (g.comp f) hgfAt :=
            mapOfEq_comp f g rfl hgfx hgfAt
          _ = mapOfEq (ContinuousMap.id X) rfl :=
            mapOfEq_congr _ _ hgf hgfAt rfl
      exact hComposite.trans hIdentity
    exact DFunLike.congr_fun hleft p
  · -- Lemma 58.1 identifies the other composite with the identity through the relative homotopy.
    intro p
    let hfgAt : (f.comp g) (f x) = f x :=
      (H.fst_eq_snd (Set.mem_singleton (f x))).symm.trans rfl
    have hright : (map f x).comp inverse = MonoidHom.id (π₁(Y, f x)) := by
      let hHomotopyEndpoint : (f.comp g) (f x) = f x :=
        (H.fst_eq_snd (Set.mem_singleton (f x))).symm.trans rfl
      have hHomotopyMap :
          mapOfEq (ContinuousMap.id Y) rfl =
            mapOfEq (f.comp g) hHomotopyEndpoint :=
        mapOfEq_eq_of_homotopicRel (ContinuousMap.id Y) (f.comp g)
          (f x) (f x) rfl H
      have hIdentity : mapOfEq (ContinuousMap.id Y) rfl =
          MonoidHom.id (π₁(Y, f x)) := mapOfEq_id Y (f x)
      have hComposite : (map f x).comp inverse =
          mapOfEq (ContinuousMap.id Y) rfl := by
        calc
          (map f x).comp inverse = (mapOfEq f rfl).comp inverse := by
            rw [mapOfEq_refl]
          _ = mapOfEq (f.comp g) hfgAt :=
            mapOfEq_comp g f hgfx rfl hfgAt
          _ = mapOfEq (f.comp g) hHomotopyEndpoint :=
            mapOfEq_congr _ _ rfl hfgAt hHomotopyEndpoint
          _ = mapOfEq (ContinuousMap.id Y) rfl :=
            hHomotopyMap.symm
      exact hComposite.trans hIdentity
    exact DFunLike.congr_fun hright p

end FundamentalGroup.LeftToRight

namespace StandardSphere

open FundamentalGroup.LeftToRight

/-- Helper for Theorem 58.2: radial projection sends a nonzero Euclidean vector
continuously to its direction on the unit sphere. -/
private theorem continuous_puncturedRadialRetraction (n : ℕ) :
    Continuous (fun x : PuncturedEuclideanSpace n ↦
      ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin (n + 1)))) x).1) := by
  -- Polar coordinates make the direction coordinate continuous.
  fun_prop

/-- Helper for Theorem 58.2: radial projection sends a nonzero Euclidean vector
to its direction on the unit sphere. -/
private noncomputable def puncturedRadialRetraction (n : ℕ) :
    C(PuncturedEuclideanSpace n, StandardSphere n) :=
  ⟨fun x ↦ ((homeomorphUnitSphereProd
      (EuclideanSpace ℝ (Fin (n + 1)))) x).1,
    continuous_puncturedRadialRetraction n⟩

/-- Helper for Theorem 58.2: radial projection is ambient normalization by the norm. -/
private theorem puncturedRadialRetraction_coe (n : ℕ)
    (x : PuncturedEuclideanSpace n) :
    (puncturedRadialRetraction n x : EuclideanSpace ℝ (Fin (n + 1))) =
      ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖⁻¹ • x := by
  -- Read the direction-coordinate computation rule from polar coordinates.
  exact homeomorphUnitSphereProd_apply_fst_coe _ x

/-- Helper for Theorem 58.2: radial projection is a strict left inverse to the
sphere inclusion. -/
private theorem puncturedRadialRetraction_comp_toPunctured (n : ℕ) :
    (puncturedRadialRetraction n).comp (toPunctured n) =
      ContinuousMap.id (StandardSphere n) := by
  -- Unit vectors are unchanged by inverse-norm scaling.
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rw [ContinuousMap.comp_apply, puncturedRadialRetraction_coe, toPunctured_apply]
  simp only [mem_sphere_zero_iff_norm.mp x.property, inv_one, one_smul,
    ContinuousMap.id_apply]

/-- Helper for Theorem 58.2: every scalar in the straight-line radial homotopy
is positive. -/
private theorem radialHomotopyScalar_pos {n : ℕ} (t : unitInterval)
    (x : PuncturedEuclideanSpace n) :
    0 < (1 - (t : ℝ)) + (t : ℝ) *
      ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖⁻¹ := by
  -- This is a convex combination of the two positive scalars `1` and `‖x‖⁻¹`.
  have hnorm : 0 < ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖⁻¹ :=
    inv_pos.mpr (norm_pos_iff.mpr x.property)
  have hleft : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.property.2
  by_cases ht : (t : ℝ) = 0
  · simp [ht]
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    exact add_pos_of_nonneg_of_pos hleft (mul_pos htpos hnorm)

/-- Helper for Theorem 58.2: the straight-line radial homotopy never reaches
the deleted origin. -/
private theorem radialHomotopyValue_ne_zero {n : ℕ}
    (p : unitInterval × PuncturedEuclideanSpace n) :
    ((1 - (p.1 : ℝ)) + (p.1 : ℝ) *
        ‖(p.2 : EuclideanSpace ℝ (Fin (n + 1)))‖⁻¹) •
        (p.2 : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 := by
  -- A positive scalar cannot annihilate the nonzero input vector.
  exact smul_ne_zero (radialHomotopyScalar_pos p.1 p.2).ne' p.2.property

/-- Helper for Theorem 58.2: the value of the straight-line homotopy from the
identity toward radial normalization. -/
private noncomputable def radialHomotopyValue (n : ℕ)
    (p : unitInterval × PuncturedEuclideanSpace n) : PuncturedEuclideanSpace n :=
  ⟨((1 - (p.1 : ℝ)) + (p.1 : ℝ) *
      ‖(p.2 : EuclideanSpace ℝ (Fin (n + 1)))‖⁻¹) •
      (p.2 : EuclideanSpace ℝ (Fin (n + 1))),
    radialHomotopyValue_ne_zero p⟩

/-- Helper for Theorem 58.2: the straight-line radial homotopy varies continuously. -/
private theorem continuous_radialHomotopyValue (n : ℕ) :
    Continuous (radialHomotopyValue n) := by
  -- Work pointwise so inverse continuity uses the stored nonzero-vector hypothesis.
  apply Continuous.subtype_mk
  rw [continuous_iff_continuousAt]
  intro p
  apply ContinuousAt.smul (M := ℝ)
  · apply ContinuousAt.add
    · fun_prop
    · apply ContinuousAt.mul
      · fun_prop
      · apply ContinuousAt.inv₀
        · fun_prop
        · exact norm_ne_zero_iff.mpr p.2.property
  · fun_prop

/-- Helper for Theorem 58.2: the radial homotopy starts at the identity. -/
private theorem radialHomotopyValue_zero (n : ℕ) (x : PuncturedEuclideanSpace n) :
    radialHomotopyValue n (0, x) = x := by
  -- At time zero the scalar coefficient reduces to one.
  apply Subtype.ext
  simp [radialHomotopyValue]

/-- Helper for Theorem 58.2: the radial homotopy ends at inclusion after radial
projection. -/
private theorem radialHomotopyValue_one (n : ℕ) (x : PuncturedEuclideanSpace n) :
    radialHomotopyValue n (1, x) =
      (toPunctured n).comp (puncturedRadialRetraction n) x := by
  -- At time one the coefficient is inverse norm, the radial projection formula.
  apply Subtype.ext
  rw [ContinuousMap.comp_apply, toPunctured_apply, puncturedRadialRetraction_coe]
  simp [radialHomotopyValue]

/-- Helper for Theorem 58.2: every sphere point remains fixed throughout the
radial homotopy. -/
private theorem radialHomotopyValue_fixed (n : ℕ) (b : StandardSphere n)
    (t : unitInterval) :
    radialHomotopyValue n (t, toPunctured n b) = toPunctured n b := by
  -- The basepoint has norm one, so every interpolating scalar is one.
  apply Subtype.ext
  simp only [radialHomotopyValue, toPunctured_apply,
    mem_sphere_zero_iff_norm.mp b.property, inv_one, mul_one]
  rw [sub_add_cancel, one_smul]

/-- Helper for Theorem 58.2: the radial homotopy is fixed on the selected
sphere basepoint. -/
private theorem radialHomotopyValue_fixedOnBasepoint (n : ℕ) (b : StandardSphere n) :
    ∀ t x, x ∈ ({toPunctured n b} : Set (PuncturedEuclideanSpace n)) →
      radialHomotopyValue n (t, x) = ContinuousMap.id _ x := by
  -- Membership in the singleton reduces the claim to the unit-norm computation.
  intro t x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  exact radialHomotopyValue_fixed n b t

/-- Helper for Theorem 58.2: the source straight-line deformation is a homotopy
relative to the selected sphere basepoint. -/
private noncomputable def puncturedRadialHomotopyRel (n : ℕ) (b : StandardSphere n) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (PuncturedEuclideanSpace n))
      ((toPunctured n).comp (puncturedRadialRetraction n)) {toPunctured n b} :=
  { toFun := radialHomotopyValue n
    continuous_toFun := continuous_radialHomotopyValue n
    map_zero_left := radialHomotopyValue_zero n
    map_one_left := radialHomotopyValue_one n
    prop' := radialHomotopyValue_fixedOnBasepoint n b }

/-- Theorem 58.2. At every basepoint, the inclusion of the standard sphere into punctured
Euclidean space induces a bijective homomorphism on fundamental groups. -/
theorem fundamentalGroupMap_bijective (n : ℕ) (b : StandardSphere n) :
    Function.Bijective (((toPunctured n)₍b₎)₊) := by
  -- Apply the abstract two-sided-inverse argument to radial projection and its relative homotopy.
  exact map_bijective_of_retractionHomotopicRel (toPunctured n)
    (puncturedRadialRetraction n) b
    (puncturedRadialRetraction_comp_toPunctured n)
    ⟨puncturedRadialHomotopyRel n b⟩

end StandardSphere

end
