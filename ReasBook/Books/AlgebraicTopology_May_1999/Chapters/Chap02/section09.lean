import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Problem_2_9_1 (from Chap02) -/
universe u

open scoped commutatorElement

noncomputable section

/-- The four standard generators in the usual presentation of the genus-2 surface group. -/
inductive GenusTwoSurfaceGenerator
  | a1
  | b1
  | a2
  | b2
deriving DecidableEq, Fintype

/-- The standard relator `[a1,b1][a2,b2]` in the free group on the genus-2 generators. -/
abbrev genus_two_surface_relator : FreeGroup GenusTwoSurfaceGenerator :=
  let a1 := FreeGroup.of GenusTwoSurfaceGenerator.a1
  let b1 := FreeGroup.of GenusTwoSurfaceGenerator.b1
  let a2 := FreeGroup.of GenusTwoSurfaceGenerator.a2
  let b2 := FreeGroup.of GenusTwoSurfaceGenerator.b2
  ⁅a1, b1⁆ * ⁅a2, b2⁆

/-- The standard presentation of the genus-2 surface group. -/
abbrev genus_two_surface_group :=
  PresentedGroup ({genus_two_surface_relator} : Set (FreeGroup GenusTwoSurfaceGenerator))

/-- The defining relator is trivial in the presented genus-2 surface group. -/
-- Proof sketch: `PresentedGroup.mk` kills every element of the chosen relation set, so the unique
-- relator `[a1,b1][a2,b2]` becomes the identity in the quotient group.
theorem genus_two_surface_group_relator_eq_one :
    PresentedGroup.mk ({genus_two_surface_relator} : Set (FreeGroup GenusTwoSurfaceGenerator))
      genus_two_surface_relator =
        (1 : genus_two_surface_group) := by
  exact PresentedGroup.one_of_mem (by simp)

private theorem genus_two_surface_lift_mem_relator_closure (w : FreeGroup Unit) :
    FreeGroup.lift (fun _ : Unit ↦ genus_two_surface_relator) w ∈
      Subgroup.closure
        ({genus_two_surface_relator} : Set (FreeGroup GenusTwoSurfaceGenerator)) := by
  refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
  · exact Subgroup.one_mem _
  · intro _
    exact Subgroup.mem_closure_singleton_self _
  · intro _ h
    simpa using Subgroup.inv_mem _ h
  · intro _ _ hx hy
    simpa using Subgroup.mul_mem _ hx hy

private theorem genus_two_surface_relator_normalClosure_range :
    Subgroup.normalClosure
        (Set.range
          (FreeGroup.lift (fun _ : Unit ↦ genus_two_surface_relator) :
            FreeGroup Unit →* FreeGroup GenusTwoSurfaceGenerator)) =
      Subgroup.normalClosure ({genus_two_surface_relator} :
        Set (FreeGroup GenusTwoSurfaceGenerator)) := by
  refine le_antisymm ?_ ?_
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨w, rfl⟩
    exact Subgroup.closure_le_normalClosure (genus_two_surface_lift_mem_relator_closure w)
  · apply Subgroup.normalClosure_mono
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact ⟨FreeGroup.of (), by simp⟩

variable {X : Type u} [TopologicalSpace X]

section

variable (U V : TopologicalSpace.Opens (TopCat.of X)) (hcover : U ⊔ V = ⊤)
variable (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
variable
  (pi1_U_equiv :
    FundamentalGroup ↥U ⟨x, hxU⟩ ≃* FreeGroup GenusTwoSurfaceGenerator)
  (pi1_inter_equiv :
    FundamentalGroup ↥(U ⊓ V) ⟨x, ⟨hxU, hxV⟩⟩ ≃* FreeGroup Unit)
variable [PathConnectedSpace ↥U] [PathConnectedSpace ↥(U ⊓ V)] [SimplyConnectedSpace V]
variable
  (attaching_map_eq :
    (pi1_U_equiv.toMonoidHom.comp (fundamental_group_inf_to_left U V x hxU hxV)).comp
        pi1_inter_equiv.symm.toMonoidHom =
      FreeGroup.lift fun _ : Unit ↦ genus_two_surface_relator)

/-- Problem 2.9.1: a based space admitting the standard genus-2 cell decomposition, equivalently
the compact surface obtained by sewing two punctured tori along their boundary circle, has
fundamental group the presented group `⟨a1, b1, a2, b2 | [a1,b1][a2,b2] = 1⟩`. -/
-- Proof sketch: apply Proposition 2.8.6 to the open cover `X = U ∪ V`. Since `V` is simply
-- connected, that proposition identifies `π₁(X, x)` with the quotient of `π₁(U, x)` by the normal
-- closure of the image of `π₁(U ∩ V, x)`. Transport the quotient through the free-group
-- identifications in `pi1_U_equiv` and `pi1_inter_equiv`, then use `attaching_map_eq` to identify
-- the killed subgroup with the normal closure of the relator `[a1,b1][a2,b2]`.
def genus_two_surface_fundamental_group
    : FundamentalGroup X x ≃* genus_two_surface_group := by
  let φ := pi1_U_equiv.toMonoidHom
  let ψ := pi1_inter_equiv.symm.toMonoidHom
  let ι := fundamental_group_inf_to_left U V x hxU hxV
  let π : FundamentalGroup ↥U ⟨x, hxU⟩ →* FundamentalGroup X x :=
    FundamentalGroup.map (TopologicalSpace.Opens.inclusion' U).hom ⟨x, hxU⟩
  have hπ_surj : Function.Surjective π :=
    fundamental_group_left_to_union_surjective U V hcover x hxU hxV
  have hπ_ker :
      π.ker =
        Subgroup.normalClosure (Set.range ι) := by
    simpa [ι] using
      fundamental_group_left_to_union_ker_eq_normal_closure_range
        U V hcover x hxU hxV
  have hrange :
      Set.range (φ.comp ι) =
        Set.range (FreeGroup.lift fun _ : Unit ↦ genus_two_surface_relator) := by
    calc
      Set.range (φ.comp ι) = Set.range ((φ.comp ι).comp ψ) := by
          ext y
          constructor
          · rintro ⟨z, rfl⟩
            exact ⟨pi1_inter_equiv z, by simp [φ, ψ]⟩
          · rintro ⟨z, rfl⟩
            exact ⟨pi1_inter_equiv.symm z, by simp [φ, ψ]⟩
      _ = Set.range (FreeGroup.lift fun _ : Unit ↦ genus_two_surface_relator) := by
          simpa only [φ, ι, ψ] using
            congrArg
              (fun f : FreeGroup Unit →* FreeGroup GenusTwoSurfaceGenerator ↦ Set.range f)
              attaching_map_eq
  have hmap_ker :
      π.ker.map φ =
        Subgroup.normalClosure ({genus_two_surface_relator} :
          Set (FreeGroup GenusTwoSurfaceGenerator)) := by
    calc
      π.ker.map φ = (Subgroup.normalClosure (Set.range ι)).map φ := by
            rw [hπ_ker]
      _ =
          Subgroup.normalClosure (φ '' Set.range ι) := by
            rw [Subgroup.map_normalClosure _ _ pi1_U_equiv.surjective]
      _ = Subgroup.normalClosure (Set.range (φ.comp ι)) := by
            congr 1
            ext y
            constructor
            · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
              exact ⟨w, rfl⟩
            · rintro ⟨w, rfl⟩
              exact ⟨_, ⟨w, rfl⟩, rfl⟩
      _ =
          Subgroup.normalClosure
            (Set.range (FreeGroup.lift fun _ : Unit ↦ genus_two_surface_relator)) := by
            rw [hrange]
      _ =
          Subgroup.normalClosure ({genus_two_surface_relator} :
            Set (FreeGroup GenusTwoSurfaceGenerator)) := by
            exact genus_two_surface_relator_normalClosure_range
  exact
    (QuotientGroup.quotientKerEquivOfSurjective π hπ_surj).symm.trans <|
      by
        simpa [genus_two_surface_group] using
          QuotientGroup.congr π.ker
            (Subgroup.normalClosure ({genus_two_surface_relator} :
              Set (FreeGroup GenusTwoSurfaceGenerator)))
            pi1_U_equiv hmap_ker

end

/-! ### Problem_2_9_2 (from Chap02) -/
universe u

open CategoryTheory
open TopologicalSpace.Opens

noncomputable section

/-- The two standard generators in the usual presentation of the Klein bottle group. -/
inductive KleinBottleGenerator
  | a
  | b
deriving DecidableEq, Fintype

/-- The standard Klein-bottle relator `aba⁻¹b` in the free group on the two generators. -/
abbrev klein_bottle_relator : FreeGroup KleinBottleGenerator :=
  let a := FreeGroup.of KleinBottleGenerator.a
  let b := FreeGroup.of KleinBottleGenerator.b
  a * b * a⁻¹ * b

/-- The standard presentation of the Klein bottle group. -/
abbrev klein_bottle_group :=
  PresentedGroup ({klein_bottle_relator} : Set (FreeGroup KleinBottleGenerator))

/-- The defining relator is trivial in the presented Klein bottle group. -/
-- Proof sketch: `PresentedGroup.mk` kills every element of the chosen relation set, so the unique
-- relator `aba⁻¹b` becomes the identity in the quotient group.
theorem klein_bottle_group_relator_eq_one :
    PresentedGroup.mk ({klein_bottle_relator} : Set (FreeGroup KleinBottleGenerator))
      klein_bottle_relator =
        (1 : klein_bottle_group) := by
  exact PresentedGroup.one_of_mem (by simp)

private theorem klein_bottle_lift_mem_relator_closure (w : FreeGroup Unit) :
    FreeGroup.lift (fun _ : Unit ↦ klein_bottle_relator) w ∈
      Subgroup.closure ({klein_bottle_relator} : Set (FreeGroup KleinBottleGenerator)) := by
  refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
  · exact Subgroup.one_mem _
  · intro _
    exact Subgroup.mem_closure_singleton_self _
  · intro _ h
    simpa using Subgroup.inv_mem _ h
  · intro _ _ hx hy
    simpa using Subgroup.mul_mem _ hx hy

private theorem klein_bottle_relator_normalClosure_range :
    Subgroup.normalClosure
        (Set.range
          (FreeGroup.lift (fun _ : Unit ↦ klein_bottle_relator) :
            FreeGroup Unit →* FreeGroup KleinBottleGenerator)) =
      Subgroup.normalClosure ({klein_bottle_relator} :
        Set (FreeGroup KleinBottleGenerator)) := by
  refine le_antisymm ?_ ?_
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨w, rfl⟩
    exact Subgroup.closure_le_normalClosure (klein_bottle_lift_mem_relator_closure w)
  · apply Subgroup.normalClosure_mono
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact ⟨FreeGroup.of (), by simp⟩

variable {X : Type u} [TopologicalSpace X]

section

variable (U V : TopologicalSpace.Opens (TopCat.of X)) (hcover : U ⊔ V = ⊤)
variable (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
variable
  (pi1_U_equiv :
    FundamentalGroup ↥U ⟨x, hxU⟩ ≃* FreeGroup KleinBottleGenerator)
  (pi1_inter_equiv :
    FundamentalGroup ↥(U ⊓ V) ⟨x, ⟨hxU, hxV⟩⟩ ≃* FreeGroup Unit)
variable [PathConnectedSpace ↥U] [PathConnectedSpace ↥(U ⊓ V)] [SimplyConnectedSpace V]
variable
  (attaching_map_eq :
    (pi1_U_equiv.toMonoidHom.comp (fundamental_group_inf_to_left U V x hxU hxV)).comp
        pi1_inter_equiv.symm.toMonoidHom =
      FreeGroup.lift fun _ : Unit ↦ klein_bottle_relator)

/-- Problem 2.9.2: a based space admitting the standard Klein-bottle decomposition, equivalently
the quotient `(S^1 × I)/(z,0) ∼ (z⁻¹,1)`, has fundamental group
`⟨a, b \mid aba^{-1}b = 1⟩`, equivalently `⟨a, b \mid aba^{-1} = b^{-1}⟩`. -/
-- Proof sketch: apply the two-open-set van Kampen theorem to the decomposition `X = U ∪ V`.
-- Because `V` is simply connected, the resulting pushout identifies `π₁(X,x)` with the quotient
-- of `π₁(U,x)` by the normal closure of the image of `π₁(U ∩ V,x)`. Transport this quotient
-- through `pi1_U_equiv` and `pi1_inter_equiv`, then use `attaching_map_eq` to identify the killed
-- subgroup with the normal closure of the single relator `aba⁻¹b`.
def klein_bottle_fundamental_group :
    FundamentalGroup X x ≃* klein_bottle_group :=
  let φ := pi1_U_equiv.toMonoidHom
  let ψ := pi1_inter_equiv.symm.toMonoidHom
  let ι := fundamental_group_inf_to_left U V x hxU hxV
  let π : FundamentalGroup ↥U ⟨x, hxU⟩ →* FundamentalGroup X x :=
    FundamentalGroup.map (inclusion' U).hom ⟨x, hxU⟩
  let hπ_surj : Function.Surjective π :=
    fundamental_group_left_to_union_surjective U V hcover x hxU hxV
  let hπ_ker :
      π.ker =
        Subgroup.normalClosure (Set.range ι) := by
    simpa [ι] using
      fundamental_group_left_to_union_ker_eq_normal_closure_range
        U V hcover x hxU hxV
  let hrange :
      Set.range (φ.comp ι) =
        Set.range (FreeGroup.lift fun _ : Unit ↦ klein_bottle_relator) := by
    calc
      Set.range (φ.comp ι) = Set.range ((φ.comp ι).comp ψ) := by
          ext y
          constructor
          · rintro ⟨z, rfl⟩
            exact ⟨pi1_inter_equiv z, by simp [φ, ψ]⟩
          · rintro ⟨z, rfl⟩
            exact ⟨pi1_inter_equiv.symm z, by simp [φ, ψ]⟩
      _ = Set.range (FreeGroup.lift fun _ : Unit ↦ klein_bottle_relator) := by
          simpa only [φ, ι, ψ] using
            congrArg
              (fun f : FreeGroup Unit →* FreeGroup KleinBottleGenerator ↦ Set.range f)
              attaching_map_eq
  let hmap_ker :
      π.ker.map φ =
        Subgroup.normalClosure ({klein_bottle_relator} :
          Set (FreeGroup KleinBottleGenerator)) := by
    calc
      π.ker.map φ = (Subgroup.normalClosure (Set.range ι)).map φ := by
            rw [hπ_ker]
      _ =
          Subgroup.normalClosure (φ '' Set.range ι) := by
            rw [Subgroup.map_normalClosure _ _ pi1_U_equiv.surjective]
      _ = Subgroup.normalClosure (Set.range (φ.comp ι)) := by
            congr 1
            ext y
            constructor
            · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
              exact ⟨w, rfl⟩
            · rintro ⟨w, rfl⟩
              exact ⟨_, ⟨w, rfl⟩, rfl⟩
      _ =
          Subgroup.normalClosure
            (Set.range (FreeGroup.lift fun _ : Unit ↦ klein_bottle_relator)) := by
            rw [hrange]
      _ =
          Subgroup.normalClosure ({klein_bottle_relator} :
            Set (FreeGroup KleinBottleGenerator)) := by
            exact klein_bottle_relator_normalClosure_range
  (QuotientGroup.quotientKerEquivOfSurjective π hπ_surj).symm.trans <|
    by
      simpa [klein_bottle_group] using
        QuotientGroup.congr π.ker
          (Subgroup.normalClosure ({klein_bottle_relator} :
            Set (FreeGroup KleinBottleGenerator)))
          pi1_U_equiv hmap_ker

end

/-! ### Problem_2_9_3 (from Chap02) -/
open scoped unitInterval ContinuousMap TopCat

noncomputable section

local notation "V[" n "]" => EuclideanSpace ℝ (Fin (n + 1))

/-- The subspace of `S^n × S^n` consisting of pairs of non-antipodal points. -/
abbrev nonantipodal_pair_space (n : ℕ) :=
  {pq : 𝕊 n × 𝕊 n | pq.1.down ≠ -pq.2.down}

-- Proof sketch: both coordinates are equal to `p`, so antipodality would force `p = -p`; taking
-- norms contradicts the defining equation `‖p‖ = 1` for points on the unit sphere.
/-- The diagonal pair `(p, p)` is non-antipodal. -/
theorem sphere_diagonal_pair_nonantipodal
    (n : ℕ) (p : 𝕊 n) : p.down ≠ -p.down := by
  simpa using ne_neg_of_mem_unit_sphere ℝ p.down

/-- The diagonal map from `S^n` to the space of non-antipodal pairs in `S^n × S^n`. -/
def sphere_diagonal_map (n : ℕ) : C(𝕊 n, nonantipodal_pair_space n) where
  toFun p := ⟨(p, p), sphere_diagonal_pair_nonantipodal n p⟩
  continuous_toFun := (continuous_id.prodMk continuous_id).subtype_mk
    (fun p ↦ sphere_diagonal_pair_nonantipodal n p)

/-- Evaluating the diagonal map returns the diagonal pair. -/
@[simp] theorem sphere_diagonal_map_apply (n : ℕ) (p : 𝕊 n) :
    sphere_diagonal_map n p =
      ⟨(p, p), sphere_diagonal_pair_nonantipodal n p⟩ :=
  rfl

/-- Helper for Problem 2.9.3: the normalization of a nonzero vector lies on the unit sphere. -/
lemma normalize_mem_unit_sphere {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {v : V} (hv : v ≠ 0) : NormedSpace.normalize v ∈ Metric.sphere (0 : V) 1 := by
  -- Turn the goal into the norm-one characterization of the unit sphere.
  simpa [mem_sphere_zero_iff_norm] using NormedSpace.norm_normalize hv

/-- Helper for Problem 2.9.3: package a nonzero vector as the corresponding point on the unit
sphere obtained by normalization. -/
def normalize_to_sphere {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (v : V) (hv : v ≠ 0) : Metric.sphere (0 : V) 1 :=
  ⟨NormedSpace.normalize v, normalize_mem_unit_sphere hv⟩

/-- Helper for Problem 2.9.3: the normalized nonzero-vector construction is continuous. -/
lemma normalize_to_sphere_map_continuous {X V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : C(X, V)) (hf : ∀ x, f x ≠ 0) :
    Continuous fun x ↦ normalize_to_sphere (f x) (hf x) := by
  -- Continuity comes from the explicit formula `normalize x = ‖x‖⁻¹ • x`.
  apply Continuous.subtype_mk
  simpa [normalize_to_sphere, NormedSpace.normalize] using
    ((continuous_norm.comp f.continuous).inv₀ fun x ↦ norm_ne_zero_iff.mpr (hf x)).smul
      f.continuous

/-- Helper for Problem 2.9.3: normalize a continuous nonvanishing vector field into the unit
sphere. -/
def normalize_to_sphere_map {X V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : C(X, V)) (hf : ∀ x, f x ≠ 0) :
    C(X, Metric.sphere (0 : V) 1) where
  toFun x := normalize_to_sphere (f x) (hf x)
  continuous_toFun := normalize_to_sphere_map_continuous f hf

/-- Helper for Problem 2.9.3: forgetting the non-antipodal condition gives a continuous map into
`S^n × S^n`. -/
def nonantipodal_pair_val_map (n : ℕ) : C(nonantipodal_pair_space n, 𝕊 n × 𝕊 n) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Helper for Problem 2.9.3: projection to the first sphere coordinate. -/
def sphere_first_projection (n : ℕ) : C(nonantipodal_pair_space n, 𝕊 n) :=
  ContinuousMap.fst.comp (nonantipodal_pair_val_map n)

/-- Helper for Problem 2.9.3: projection to the second sphere coordinate. -/
def sphere_second_projection (n : ℕ) : C(nonantipodal_pair_space n, 𝕊 n) :=
  ContinuousMap.snd.comp (nonantipodal_pair_val_map n)

/-- Helper for Problem 2.9.3: the ambient straight-line segment from `p` to `q`. -/
def sphere_segment_vector (n : ℕ) (t : ℝ) (p q : 𝕊 n) : V[n] :=
  (1 - t) • ((p.down : Metric.sphere (0 : V[n]) 1) : V[n]) +
    t • ((q.down : Metric.sphere (0 : V[n]) 1) : V[n])

/-- Helper for Problem 2.9.3: a non-antipodal pair has no zero convex combination on the segment
joining its endpoints on the sphere. -/
lemma sphere_segment_vector_ne_zero (n : ℕ) {p q : 𝕊 n} (h : p.down ≠ -q.down)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    sphere_segment_vector n t p q ≠ 0 := by
  let pv : V[n] := (p.down : Metric.sphere (0 : V[n]) 1)
  let qv : V[n] := (q.down : Metric.sphere (0 : V[n]) 1)
  intro hw
  have hw' : t • qv + (1 - t) • pv = 0 := by
    simpa [sphere_segment_vector, pv, qv, add_comm] using hw
  have hEq : t • qv = -((1 - t) • pv) := eq_neg_of_add_eq_zero_left hw'
  -- Compare norms to force the convex coefficients to coincide.
  have hnorm' : |t| = |1 - t| := by
    have := congrArg norm hEq
    simpa [pv, qv, norm_smul] using this
  have hnorm : t = 1 - t := by
    rwa [abs_of_nonneg ht0, abs_of_nonneg (sub_nonneg.mpr ht1)] at hnorm'
  have hnorm2 : 1 - t = t := hnorm.symm
  have ht_pos : 0 < t := by
    by_contra ht
    have ht' : t = 0 := by linarith
    linarith [hnorm]
  have hqv : qv = -pv := by
    apply (smul_right_injective (M := V[n]) (show t ≠ 0 by linarith))
    calc
      t • qv = -((1 - t) • pv) := hEq
      _ = t • (-pv) := by rw [hnorm2, smul_neg]
  have hpv : pv = -qv := by
    simpa [eq_comm] using congrArg Neg.neg hqv
  have hcontra : p.down = -q.down := by
    apply Subtype.ext
    simpa [pv, qv] using hpv
  exact h hcontra

/-- Helper for Problem 2.9.3: the normalized point on the straight-line segment from `p` to `q`. -/
def sphere_segment_point (n : ℕ) (t : ℝ) (p q : 𝕊 n) (h : p.down ≠ -q.down)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Metric.sphere (0 : V[n]) 1 :=
  normalize_to_sphere (sphere_segment_vector n t p q) (sphere_segment_vector_ne_zero n h ht0 ht1)

/-- Helper for Problem 2.9.3: at time `0`, the normalized segment returns the first endpoint. -/
@[simp] lemma sphere_segment_point_zero (n : ℕ) (p q : 𝕊 n) (h : p.down ≠ -q.down) :
    sphere_segment_point n 0 p q h le_rfl zero_le_one = p.down := by
  -- The segment vector is exactly `p`, so normalization fixes it.
  apply Subtype.ext
  simp [sphere_segment_point, sphere_segment_vector, normalize_to_sphere,
    NormedSpace.normalize_eq_self_of_norm_eq_one]

/-- Helper for Problem 2.9.3: at time `1`, the normalized segment returns the second endpoint. -/
@[simp] lemma sphere_segment_point_one (n : ℕ) (p q : 𝕊 n) (h : p.down ≠ -q.down) :
    sphere_segment_point n 1 p q h zero_le_one le_rfl = q.down := by
  -- The segment vector is exactly `q`, so normalization fixes it.
  apply Subtype.ext
  simp [sphere_segment_point, sphere_segment_vector, normalize_to_sphere,
    NormedSpace.normalize_eq_self_of_norm_eq_one]

/-- Helper for Problem 2.9.3: the normalized segment never lands at the antipode of the initial
point. -/
lemma sphere_segment_point_ne_neg_left (n : ℕ) {p q : 𝕊 n} (h : p.down ≠ -q.down)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    sphere_segment_point n t p q h ht0 ht1 ≠ -p.down := by
  let pv : V[n] := (p.down : Metric.sphere (0 : V[n]) 1)
  let qv : V[n] := (q.down : Metric.sphere (0 : V[n]) 1)
  let w : V[n] := sphere_segment_vector n t p q
  intro hneg
  have hvec : NormedSpace.normalize w = -(pv : V[n]) := by
    exact congrArg Subtype.val hneg
  have hw_eq : w = -(‖w‖ • pv) := by
    -- Rewrite the segment vector using the assumed antipodality of its normalization.
    calc
      w = ‖w‖ • NormedSpace.normalize w := by simp [w]
      _ = -(‖w‖ • pv) := by rw [hvec, smul_neg]
  have hsum : t • qv + ((1 - t) + ‖w‖) • pv = 0 := by
    have hsum0 : w + ‖w‖ • pv = 0 := eq_neg_iff_add_eq_zero.mp hw_eq
    simpa [sphere_segment_vector, pv, qv, w, add_assoc, add_left_comm, add_comm, add_smul] using
      hsum0
  have hw_eq' : t • qv = -(((1 - t) + ‖w‖) • pv) := eq_neg_of_add_eq_zero_left hsum
  -- Norms now identify the positive coefficient of `pv` with the coefficient `t` of `qv`.
  have hnorm : t = (1 - t) + ‖w‖ := by
    have := congrArg norm hw_eq'
    simpa [pv, qv, norm_smul, abs_of_nonneg ht0,
      abs_of_nonneg (add_nonneg (sub_nonneg.mpr ht1) (norm_nonneg _))] using this
  have hnorm2 : (1 - t) + ‖w‖ = t := hnorm.symm
  have hqv : qv = -pv := by
    apply (smul_right_injective (M := V[n]) (show t ≠ 0 by
      intro ht
      linarith [norm_nonneg w]))
    calc
      t • qv = -(((1 - t) + ‖w‖) • pv) := hw_eq'
      _ = t • (-pv) := by rw [hnorm2, smul_neg]
  have hpv : pv = -qv := by
    simpa [eq_comm] using congrArg Neg.neg hqv
  have hcontra : p.down = -q.down := by
    apply Subtype.ext
    simpa [pv, qv] using hpv
  exact h hcontra

/-- Helper for Problem 2.9.3: the ambient segment vector varies continuously with time and the
non-antipodal pair. -/
lemma sphere_segment_vector_map_continuous (n : ℕ) :
    Continuous fun x : unitInterval × nonantipodal_pair_space n =>
      sphere_segment_vector n x.1 x.2.1.1 x.2.1.2 := by
  -- This is a direct continuity check for the explicit affine formula.
  simpa [sphere_segment_vector] using
    (show Continuous fun x : unitInterval × nonantipodal_pair_space n =>
      (1 - (x.1 : ℝ)) • (((x.2.1.1).down : Metric.sphere (0 : V[n]) 1) : V[n]) +
        (x.1 : ℝ) • (((x.2.1.2).down : Metric.sphere (0 : V[n]) 1) : V[n]) by
      fun_prop)

/-- Helper for Problem 2.9.3: the ambient segment vector as a continuous map. -/
def sphere_segment_vector_map (n : ℕ) : C(unitInterval × nonantipodal_pair_space n, V[n]) where
  toFun x := sphere_segment_vector n x.1 x.2.1.1 x.2.1.2
  continuous_toFun := sphere_segment_vector_map_continuous n

/-- Helper for Problem 2.9.3: the normalized segment as a continuous map into the raw sphere. -/
def sphere_segment_raw_map (n : ℕ) :
    C(unitInterval × nonantipodal_pair_space n, Metric.sphere (0 : V[n]) 1) :=
  normalize_to_sphere_map (sphere_segment_vector_map n)
    (fun x ↦ sphere_segment_vector_ne_zero n x.2.2 x.1.2.1 x.1.2.2)

/-- Helper for Problem 2.9.3: the normalized segment as a continuous map into `S^n`. -/
def sphere_segment_map (n : ℕ) : C(unitInterval × nonantipodal_pair_space n, 𝕊 n) :=
  ⟨ULift.up ∘ sphere_segment_raw_map n, continuous_uliftUp.comp (sphere_segment_raw_map n).continuous⟩

/-- Helper for Problem 2.9.3: the segment homotopy starts at the first projection. -/
lemma sphere_segment_map_zero (n : ℕ) (pq : nonantipodal_pair_space n) :
    sphere_segment_map n (0, pq) = sphere_first_projection n pq := by
  -- Unwrap the `ULift` and use the `t = 0` endpoint computation.
  apply ULift.ext
  change sphere_segment_point n 0 pq.1.1 pq.1.2 pq.2 le_rfl zero_le_one = pq.1.1.down
  exact sphere_segment_point_zero n pq.1.1 pq.1.2 pq.2

/-- Helper for Problem 2.9.3: the segment homotopy ends at the second projection. -/
lemma sphere_segment_map_one (n : ℕ) (pq : nonantipodal_pair_space n) :
    sphere_segment_map n (1, pq) = sphere_second_projection n pq := by
  -- Unwrap the `ULift` and use the `t = 1` endpoint computation.
  apply ULift.ext
  change sphere_segment_point n 1 pq.1.1 pq.1.2 pq.2 zero_le_one le_rfl = pq.1.2.down
  exact sphere_segment_point_one n pq.1.1 pq.1.2 pq.2

/-- Helper for Problem 2.9.3: the normalized segment gives a homotopy from the first projection to
the second projection. -/
def sphere_second_coordinate_homotopy (n : ℕ) :
    (sphere_first_projection n).Homotopy (sphere_second_projection n) where
  toContinuousMap := sphere_segment_map n
  map_zero_left := sphere_segment_map_zero n
  map_one_left := sphere_segment_map_one n

/-- Helper for Problem 2.9.3: the product deformation keeps the first coordinate fixed and moves
the second coordinate along the normalized segment. -/
def sphere_pair_deformation_product_map (n : ℕ) :
    C(unitInterval × nonantipodal_pair_space n, 𝕊 n × 𝕊 n) :=
  ((sphere_first_projection n).comp ContinuousMap.snd).prodMk (sphere_segment_map n)

/-- Helper for Problem 2.9.3: the product deformation always lands back in the non-antipodal
subspace. -/
lemma sphere_pair_deformation_product_map_mem (n : ℕ) (x : unitInterval × nonantipodal_pair_space n) :
    (sphere_pair_deformation_product_map n x).1.down ≠ -(sphere_pair_deformation_product_map n x).2.down := by
  -- This is exactly the non-antipodality lemma for the normalized segment.
  change x.2.1.1.down ≠ -(sphere_segment_raw_map n x)
  intro hneg
  have hneg' : sphere_segment_raw_map n x = -x.2.1.1.down := by
    simpa [eq_comm] using congrArg Neg.neg hneg
  exact sphere_segment_point_ne_neg_left n x.2.2 x.1.2.1 x.1.2.2 (by
    simpa [sphere_segment_raw_map, sphere_segment_point] using hneg')

/-- Helper for Problem 2.9.3: the fixed-first-coordinate deformation is pointwise non-antipodal. -/
lemma sphere_pair_deformation_nonantipodal (n : ℕ) (x : unitInterval × nonantipodal_pair_space n) :
    x.2.1.1.down ≠ -(sphere_segment_map n x).down := by
  -- This is exactly the same normalization argument as above, specialized to the fixed first
  -- coordinate.
  intro hneg
  have hneg' : sphere_segment_raw_map n x = -x.2.1.1.down := by
    simpa [sphere_segment_map, sphere_segment_raw_map, eq_comm] using congrArg Neg.neg hneg
  exact sphere_segment_point_ne_neg_left n x.2.2 x.1.2.1 x.1.2.2 (by
    simpa [sphere_segment_raw_map, sphere_segment_point] using hneg')

/-- Helper for Problem 2.9.3: the product deformation viewed as a continuous map into the
non-antipodal pair space. -/
def sphere_pair_deformation_map (n : ℕ) :
    C(unitInterval × nonantipodal_pair_space n, nonantipodal_pair_space n) := by
  refine
    { toFun := fun x ↦ ?_
      continuous_toFun := ?_ }
  let q : 𝕊 n := sphere_segment_map n x
  refine ⟨(x.2.1.1, q), ?_⟩
  intro hneg
  have hneg' : sphere_segment_raw_map n x = -x.2.1.1.down := by
    simpa [q, sphere_segment_map, sphere_segment_raw_map, eq_comm] using congrArg Neg.neg hneg
  exact sphere_segment_point_ne_neg_left n x.2.2 x.1.2.1 x.1.2.2 (by
    simpa [q, sphere_segment_raw_map, sphere_segment_point] using hneg')
  exact Continuous.subtype_mk
    (show Continuous fun x : unitInterval × nonantipodal_pair_space n =>
      (x.2.1.1, sphere_segment_map n x) by
      fun_prop)
    (fun x ↦ by
      intro hneg
      have hneg' : sphere_segment_raw_map n x = -x.2.1.1.down := by
        simpa [sphere_segment_map, sphere_segment_raw_map, eq_comm] using congrArg Neg.neg hneg
      exact sphere_segment_point_ne_neg_left n x.2.2 x.1.2.1 x.1.2.2 (by
        simpa [sphere_segment_raw_map, sphere_segment_point] using hneg'))

/-- Helper for Problem 2.9.3: the product deformation starts at the diagonal of the first
projection. -/
lemma sphere_pair_deformation_zero (n : ℕ) (pq : nonantipodal_pair_space n) :
    sphere_pair_deformation_map n (0, pq) =
      ((sphere_diagonal_map n).comp (sphere_first_projection n)) pq := by
  -- Compare the underlying pair and then use the `t = 0` endpoint for the moving coordinate.
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · simpa [sphere_pair_deformation_map, sphere_pair_deformation_product_map, sphere_diagonal_map]
      using sphere_segment_map_zero n pq

/-- Helper for Problem 2.9.3: the product deformation ends at the identity map. -/
lemma sphere_pair_deformation_one (n : ℕ) (pq : nonantipodal_pair_space n) :
    sphere_pair_deformation_map n (1, pq) = ContinuousMap.id (nonantipodal_pair_space n) pq := by
  -- Again compare the underlying pair and use the `t = 1` endpoint for the moving coordinate.
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · simpa [sphere_pair_deformation_map, sphere_pair_deformation_product_map, sphere_second_projection]
      using sphere_segment_map_one n pq

/-- Helper for Problem 2.9.3: the first projection is a right homotopy inverse to the diagonal
map. -/
def sphere_first_projection_right_homotopy (n : ℕ) :
    ((sphere_diagonal_map n).comp (sphere_first_projection n)).Homotopy
      (ContinuousMap.id (nonantipodal_pair_space n)) where
  toContinuousMap := sphere_pair_deformation_map n
  map_zero_left := sphere_pair_deformation_zero n
  map_one_left := sphere_pair_deformation_one n

-- Proof sketch: a homotopy inverse is given by the normalized midpoint map
-- `(p, q) ↦ (p + q) / ‖p + q‖`;
-- the condition `p ≠ -q` ensures the midpoint is defined, and straight-line normalization gives the
-- two required homotopies.
/-- Problem 2.9.3: the diagonal map `p ↦ (p, p)` from `S^n` to the space of non-antipodal pairs in
`S^n × S^n` is the forward map of a homotopy equivalence. -/
theorem sphere_diagonal_map_homotopy_equiv (n : ℕ) :
    ∃ e : 𝕊 n ≃ₕ nonantipodal_pair_space n,
      e.toFun = sphere_diagonal_map n := by
  -- Route correction: keeping the first coordinate fixed makes the inverse exactly the first
  -- projection, and the normalized segment supplies the required right homotopy.
  refine ⟨{ toFun := sphere_diagonal_map n
            invFun := sphere_first_projection n
            left_inv := ?_
            right_inv := ⟨sphere_first_projection_right_homotopy n⟩ }, rfl⟩
  -- The left inverse is definitional once we project a diagonal pair.
  refine ⟨(ContinuousMap.Homotopy.refl (ContinuousMap.id (𝕊 n))).cast ?_ rfl⟩
  ext p
  rfl

/-! ### Problem_2_9_4 (from Chap02) -/
universe v u

open CategoryTheory Limits

/- Problem 2.9.4 (1): any category with all coproducts and coequalizers is cocomplete, as
expressed by the canonical theorem constructing all colimits from these two classes of colimits. -/
recall has_colimits_of_hasCoequalizers_and_coproducts {C : Type u} [Category.{v} C]
    [HasCoproducts.{v} C] [HasCoequalizers C] : HasColimits C

/- Problem 2.9.4 (2): by passage to opposite categories, the dual statement says that products and
equalizers imply completeness, as recorded by the canonical theorem constructing all limits from
these two classes of limits. -/
recall has_limits_of_hasEqualizers_and_products {C : Type u} [Category.{v} C]
    [HasProducts.{v} C] [HasEqualizers C] : HasLimits C
