import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_1_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Bundle

-- Semantic recall: `OnePoint` is the canonical fiberwise compactification owner, but the Thom
-- space must use the topology coming from the actual vector-bundle atlas rather than the coproduct
-- topology on a raw sigma type. The file therefore models the fiberwise compactification by a
-- one-point-compactified bundle total space. Definition 23.5.1 (2) keeps the all-ranks pointed
-- disk quotient as the primary metric model, while the positive-rank literal disk/sphere quotient
-- remains a companion recovered by explicit comparison maps rather than choice-built equivalences.

section

variable {B : Type u} {n : ℕ} {E : B → Type v}

/-- The bundle obtained by one-point compactifying each fiber of `E`. -/
abbrev ThomFiber (E : B → Type v) := fun b : B ↦ OnePoint (E b)

/-- The total space of the one-point compactified bundle attached to `E`. -/
abbrev ThomPreSpace (n : ℕ) (E : B → Type v) :=
  Bundle.TotalSpace (OnePoint (Fin n → ℝ)) (ThomFiber E)

/-- The relation on `ThomPreSpace n E` identifying equal points and collapsing all fiberwise points
at infinity to a single class. -/
def thomSpaceRel (n : ℕ) (E : B → Type v) (x y : ThomPreSpace n E) : Prop :=
  x = y ∨ (x.2 = OnePoint.infty ∧ y.2 = OnePoint.infty)

/-- The Thom-space relation is reflexive. -/
theorem thomSpaceRel_refl (n : ℕ) (E : B → Type v) (x : ThomPreSpace n E) :
    thomSpaceRel n E x x := by
  -- Equality is one branch of the Thom-space collapse relation.
  exact Or.inl rfl

/-- The Thom-space relation is symmetric. -/
theorem thomSpaceRel_symm (n : ℕ) (E : B → Type v) {x y : ThomPreSpace n E} :
    thomSpaceRel n E x y → thomSpaceRel n E y x := by
  -- The only non-equality case is simultaneous infinity, which is manifestly symmetric.
  intro hxy
  rcases hxy with rfl | ⟨hx, hy⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hy, hx⟩

/-- The Thom-space relation is transitive. -/
theorem thomSpaceRel_trans (n : ℕ) (E : B → Type v) {x y z : ThomPreSpace n E} :
    thomSpaceRel n E x y → thomSpaceRel n E y z → thomSpaceRel n E x z := by
  -- Once both intermediate witnesses are in the collapsed infinity class, the endpoints are too.
  intro hxy hyz
  rcases hxy with rfl | ⟨hx, hy⟩
  · exact hyz
  rcases hyz with rfl | ⟨hy', hz⟩
  · exact Or.inr ⟨hx, hy⟩
  · exact Or.inr ⟨hx, hz⟩

/-- The quotient relation collapsing all fiberwise points at infinity to one point. -/
def thomSpaceSetoid (n : ℕ) (E : B → Type v) : Setoid (ThomPreSpace n E) where
  r := thomSpaceRel n E
  iseqv := ⟨thomSpaceRel_refl n E, thomSpaceRel_symm n E, thomSpaceRel_trans n E⟩

/-- For Definition 23.5.1 (1), `ThomSpace n E` is the Thom space `T(ξ)` obtained by one-point
compactifying each fiber and then identifying the added points at infinity. -/
abbrev ThomSpace (n : ℕ) (E : B → Type v) :=
  Quotient (thomSpaceSetoid n E)

/-- The class in `ThomSpace n E` represented by a chosen point in the compactified fiber over
`b`. -/
abbrev thomSpaceMk (n : ℕ) (E : B → Type v) (b : B) (x : OnePoint (E b)) :
    ThomSpace n E :=
  Quotient.mk (thomSpaceSetoid n E) (⟨b, x⟩ : ThomPreSpace n E)

/-- Any two fiberwise points at infinity represent the same point of `ThomSpace n E`. -/
theorem thomSpaceMk_infty_eq (n : ℕ) (E : B → Type v) (b₁ b₂ : B) :
    thomSpaceMk n E b₁ (OnePoint.infty : OnePoint (E b₁)) =
      thomSpaceMk n E b₂ (OnePoint.infty : OnePoint (E b₂)) := by
  -- The quotient collapses all fiberwise points at infinity to one class.
  exact Quotient.sound <| Or.inr ⟨rfl, rfl⟩

end

section

variable {B : Type u} {n : ℕ} {E : B → Type v}

-- The topological structure on `ThomSpace n E` is introduced later, after the uniform disk and
-- disk/sphere quotient models have been compared by explicit equivalences.

variable (E) (n)
variable [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]

/-- The closed unit disk bundle in the chosen fiberwise norm on `E`, formed inside the actual
bundle total space. -/
abbrev ThomDiskBundle :=
  {x : Bundle.TotalSpace (Fin n → ℝ) E // ‖x.2‖ ≤ 1}

/-- The unit sphere bundle in the chosen fiberwise norm on `E`, viewed as a locus in the closed
unit disk bundle. -/
def thomSphereLocus : Set (ThomDiskBundle n E) :=
  {x | ‖x.1.2‖ = 1}

/-- The relation on the closed unit disk bundle identifying equal points and collapsing the unit
sphere bundle to one point. -/
def thomDiskBundleRel (n : ℕ) (E : B → Type v) [∀ b, NormedAddCommGroup (E b)]
    (x y : ThomDiskBundle n E) : Prop :=
  x = y ∨ (x ∈ thomSphereLocus n E ∧ y ∈ thomSphereLocus n E)

/-- The setoid on the closed unit disk bundle collapsing the unit sphere bundle to a single
quotient class. -/
def thomDiskBundleSetoid (n : ℕ) (E : B → Type v) [∀ b, NormedAddCommGroup (E b)] :
    Setoid (ThomDiskBundle n E) where
  r := thomDiskBundleRel n E
  iseqv := by
    -- The sphere-collapse relation is equality plus a common membership condition.
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact Or.inl rfl
    · intro x y hxy
      rcases hxy with rfl | ⟨hx, hy⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hy, hx⟩
    · intro x y z hxy hyz
      rcases hxy with rfl | hxy
      · exact hyz
      rcases hyz with rfl | hyz
      · exact Or.inr hxy
      · exact Or.inr ⟨hxy.1, hyz.2⟩

/-- The literal quotient `D(E) / S(E)` of the closed unit disk bundle by its unit sphere bundle. -/
abbrev ThomDiskSphereQuotient (n : ℕ) (E : B → Type v) [∀ b, NormedAddCommGroup (E b)] :
    Type (max u v) :=
  Quotient (thomDiskBundleSetoid n E)

/-- The rank-`n` fiberwise pointed closed-disk prequotient adjoining a point at infinity to each
closed unit disk fiber. This is auxiliary helper API for comparing the literal disk/sphere
quotient with the one-point-compactification model. -/
abbrev ThomDiskPreSpace (n : ℕ) (E : B → Type v) [∀ b, NormedAddCommGroup (E b)] :=
  let _ := n
  Sigma fun b : B ↦ OnePoint ({v : E b // ‖v‖ ≤ 1})

/-- The relation on the rank-`n` fiberwise pointed closed unit disk bundle that collapses the unit
sphere bundle together with the added fiberwise points at infinity to one point. -/
def thomDiskRel (n : ℕ) (E : B → Type v) [∀ b, NormedAddCommGroup (E b)]
    (x y : ThomDiskPreSpace n E) : Prop :=
  x = y ∨
    (((x.2 = OnePoint.infty) ∨
        ∃ vx : {v : E x.1 // ‖v‖ ≤ 1}, x.2 = OnePoint.some vx ∧ ‖vx.1‖ = 1) ∧
      ((y.2 = OnePoint.infty) ∨
        ∃ vy : {v : E y.1 // ‖v‖ ≤ 1}, y.2 = OnePoint.some vy ∧ ‖vy.1‖ = 1))

/-- The quotient of the auxiliary pointed closed unit disk bundle obtained by collapsing the unit
sphere bundle together with the added points at infinity to one point. -/
def thomDiskSetoid (n : ℕ) (E : B → Type v) [∀ b, NormedAddCommGroup (E b)] :
    Setoid (ThomDiskPreSpace n E) where
  r := thomDiskRel n E
  iseqv := by
    -- The pointed disk relation again splits into equality or simultaneous membership
    -- in the collapsed boundary-or-infinity class.
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact Or.inl rfl
    · intro x y hxy
      rcases hxy with rfl | ⟨hx, hy⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hy, hx⟩
    · intro x y z hxy hyz
      rcases hxy with rfl | hxy
      · exact hyz
      rcases hyz with rfl | hyz
      · exact Or.inr hxy
      · exact Or.inr ⟨hxy.1, hyz.2⟩

/-- An auxiliary pointed quotient attached to the closed unit disk bundle, obtained by also
collapsing the added fiberwise points at infinity. -/
abbrev ThomDiskQuotient (n : ℕ) (E : B → Type v) [∀ b, NormedAddCommGroup (E b)] :
    Type (max u v) :=
  Quotient (thomDiskSetoid n E)

/-- Helper for Definition 23.5.1: nonnegative real scaling pulls out of the norm on each fiber
`E b`. -/
theorem fiberNormSmul_of_nonneg {b : B} (t : ℝ) (ht : 0 ≤ t) (v : E b) :
    ‖(t • v : E b)‖ = t * ‖v‖ := by
  -- `norm_smul` reduces the claim to the nonnegative real scalar identity `‖t‖ = t`.
  simpa using norm_smul_of_nonneg ht v

/-- The radial rescaling `v ↦ (1 / (1 + ‖v‖)) • v` lands in the closed unit disk of the fiber
over `b`. -/
theorem thomDiskBundleRadialPoint_mem (b : B) (v : E b) :
    ‖((1 / (1 + ‖v‖)) • v : E b)‖ ≤ 1 := by
  -- Rewrite the radial norm as `‖v‖ / (1 + ‖v‖)` before comparing numerator and denominator.
  have hscale_nonneg : 0 ≤ (1 / (1 + ‖v‖) : ℝ) := by
    positivity
  rw [fiberNormSmul_of_nonneg (E := E) (b := b) (1 / (1 + ‖v‖)) hscale_nonneg v]
  have hle : ‖v‖ ≤ 1 + ‖v‖ := by
    linarith
  have hmul :
      (1 / (1 + ‖v‖) : ℝ) * ‖v‖ ≤ (1 / (1 + ‖v‖) : ℝ) * (1 + ‖v‖) := by
    exact mul_le_mul_of_nonneg_left hle hscale_nonneg
  have hden : (1 + ‖v‖ : ℝ) ≠ 0 := by
    positivity
  calc
    (1 / (1 + ‖v‖) : ℝ) * ‖v‖ ≤ (1 / (1 + ‖v‖) : ℝ) * (1 + ‖v‖) := hmul
    _ = 1 := one_div_mul_cancel hden

/-- The closed-disk representative obtained by radially rescaling a fiber vector. -/
noncomputable def thomDiskBundleRadialPoint (b : B) (v : E b) : ThomDiskBundle n E :=
  ⟨⟨b, (1 / (1 + ‖v‖)) • v⟩, thomDiskBundleRadialPoint_mem E b v⟩

section ModelVector

variable [TopologicalSpace B]
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
variable [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
variable [VectorBundle ℝ (Fin n → ℝ) E]

/-- A chosen nonzero fiber vector obtained by transporting the first standard basis vector of
`Fin n → ℝ` into the fiber over `b`. -/
noncomputable def thomFiberModelVector (hn : 0 < n) (b : B) : E b :=
  let e := VectorBundle.continuousLinearEquivAt ℝ (Fin n → ℝ) E b
  e.symm (Pi.single ⟨0, hn⟩ (1 : ℝ))

/-- The transported model vector in the fiber over `b` is nonzero. -/
theorem thomFiberModelVector_ne_zero (hn : 0 < n) (b : B) :
    thomFiberModelVector n E hn b ≠ 0 := by
  -- Push the model vector through the preferred fiber equivalence and read off the first
  -- coordinate in `Fin n → ℝ`.
  let i : Fin n := ⟨0, hn⟩
  let e := VectorBundle.continuousLinearEquivAt ℝ (Fin n → ℝ) E b
  intro hzero
  have hsingle : (Pi.single i (1 : ℝ) : Fin n → ℝ) = 0 := by
    apply (e.symm.map_eq_zero_iff).mp
    simpa [thomFiberModelVector, e, i] using hzero
  have hcoord : (1 : ℝ) = 0 := by
    simpa [Pi.single_apply, i] using congrArg (fun f : Fin n → ℝ => f i) hsingle
  exact one_ne_zero hcoord

/-- A chosen unit vector in the fiber over `b`, obtained by normalizing the transported model
vector. -/
noncomputable def thomSphereVector (hn : 0 < n) (b : B) : E b :=
  ‖thomFiberModelVector n E hn b‖⁻¹ • thomFiberModelVector n E hn b

/-- The chosen normalized fiber vector has norm `1`. -/
theorem thomSphereVector_norm (hn : 0 < n) (b : B) :
    ‖thomSphereVector n E hn b‖ = 1 := by
  -- Normalize the nonzero transported model vector by its inverse norm.
  let v := thomFiberModelVector n E hn b
  have hv : v ≠ 0 := thomFiberModelVector_ne_zero (n := n) (E := E) hn b
  have hv' : v ≠ (0 : E b) := by
    intro hzero
    exact hv hzero
  simpa [thomSphereVector, v] using (norm_smul_inv_norm (𝕜 := ℝ) (x := v) hv')

/-- The chosen normalized fiber vector lies in the closed unit disk bundle. -/
theorem thomSphereVector_mem_disk (hn : 0 < n) (b : B) :
    ‖thomSphereVector n E hn b‖ ≤ 1 := by
  -- The chosen vector has norm exactly `1`.
  rw [thomSphereVector_norm n E hn b]

/-- A chosen point of the unit sphere bundle over `b`. -/
noncomputable def thomSphereBundlePoint (hn : 0 < n) (b : B) : ThomDiskBundle n E :=
  ⟨⟨b, thomSphereVector n E hn b⟩, thomSphereVector_mem_disk n E hn b⟩

/-- The chosen point of the disk bundle lies on the unit sphere locus. -/
theorem thomSphereBundlePoint_mem_locus (hn : 0 < n) (b : B) :
    thomSphereBundlePoint n E hn b ∈ thomSphereLocus n E := by
  -- Membership in the sphere locus is exactly the norm-one condition.
  simpa [thomSphereLocus, thomSphereBundlePoint] using thomSphereVector_norm n E hn b

end ModelVector

/-- Helper for Definition 23.5.1: radial compactification rescales the norm by
`t ↦ (1 / (1 + t)) * t`. -/
theorem thomRadial_norm_eq (b : B) (v : E b) :
    ‖((1 / (1 + ‖v‖)) • v : E b)‖ = (1 / (1 + ‖v‖) : ℝ) * ‖v‖ := by
  -- State the scalar action in the exact form expected by `norm_smul_of_nonneg`.
  have hscale_nonneg : 0 ≤ (1 / (1 + ‖v‖) : ℝ) := by
    positivity
  simpa using fiberNormSmul_of_nonneg (E := E) (b := b) (1 / (1 + ‖v‖)) hscale_nonneg v

/-- Helper for Definition 23.5.1: inverse radial compactification rescales the norm on the closed
disk by `t ↦ (1 / (1 - t)) * t`. -/
theorem thomInverseRadial_norm_eq {b : B} (v : {v : E b // ‖v‖ ≤ 1}) :
    ‖(((1 - ‖v.1‖)⁻¹ : ℝ) • v.1 : E b)‖ = ((1 - ‖v.1‖)⁻¹ : ℝ) * ‖v.1‖ := by
  -- Closed-disk membership makes the inverse-radial scalar nonnegative.
  have hscale_nonneg : 0 ≤ ((1 - ‖v.1‖)⁻¹ : ℝ) := by
    apply inv_nonneg.mpr
    linarith [v.2]
  simpa using fiberNormSmul_of_nonneg (E := E) (b := b) ((1 - ‖v.1‖)⁻¹) hscale_nonneg v.1

/-- Helper for Definition 23.5.1: the radial rescaling lands strictly inside the unit disk. -/
theorem thomRadial_norm_lt_one (b : B) (v : E b) :
    ‖((1 / (1 + ‖v‖)) • v : E b)‖ < 1 := by
  -- After rewriting to `‖v‖ / (1 + ‖v‖)`, the denominator is strictly larger than the numerator.
  rw [thomRadial_norm_eq]
  have hpos : (0 : ℝ) < 1 + ‖v‖ := by positivity
  have hlt : ‖v‖ < 1 + ‖v‖ := by linarith
  have hdiv : ‖v‖ / (1 + ‖v‖) < (1 : ℝ) := by
    exact (div_lt_one hpos).2 hlt
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

/-- Helper for Definition 23.5.1: the radial rescaling never lands on the boundary sphere. -/
theorem thomRadial_norm_ne_one (b : B) (v : E b) :
    ‖((1 / (1 + ‖v‖)) • v : E b)‖ ≠ 1 :=
  by
    -- Strict interior immediately rules out the boundary value.
    exact ne_of_lt (thomRadial_norm_lt_one (E := E) b v)

/-- Helper for Definition 23.5.1: inverse radial compactification undoes radial compactification
on every fiber. -/
theorem inverseRadial_comp_radial (b : B) (v : E b) :
    (((1 - ‖((1 / (1 + ‖v‖)) • v : E b)‖)⁻¹ : ℝ) • ((1 / (1 + ‖v‖)) • v) : E b) = v := by
  -- Rewrite the intermediate norm and collapse the resulting scalar product to `1`.
  have hden : (1 + ‖v‖ : ℝ) ≠ 0 := by positivity
  have hscalar :
      (1 - ((1 / (1 + ‖v‖) : ℝ) * ‖v‖) : ℝ) = (1 / (1 + ‖v‖) : ℝ) := by
    field_simp [hden]
    ring
  rw [thomRadial_norm_eq, hscalar, smul_smul, inv_mul_cancel₀, one_smul]
  exact one_div_ne_zero hden

/-- Helper for Definition 23.5.1: radial compactification undoes inverse radial compactification
for a closed-disk point away from the boundary. -/
theorem radial_comp_inverseRadial {b : B} (v : {v : E b // ‖v‖ ≤ 1}) (hneq : ‖v.1‖ ≠ 1) :
    ((1 / (1 + ‖(((1 - ‖v.1‖)⁻¹ : ℝ) • v.1 : E b)‖) : ℝ) •
        (((1 - ‖v.1‖)⁻¹ : ℝ) • v.1) : E b) = v.1 := by
  -- Away from the boundary, the inverse-radial scalar is well defined and the composite scalar
  -- simplifies back to `1`.
  have hlt : ‖v.1‖ < (1 : ℝ) := lt_of_le_of_ne v.2 hneq
  have hsub : (1 - ‖v.1‖ : ℝ) ≠ 0 := by linarith
  have hscalar :
      (1 + ((1 - ‖v.1‖)⁻¹ : ℝ) * ‖v.1‖ : ℝ) = ((1 - ‖v.1‖)⁻¹ : ℝ) := by
    field_simp [hsub]
    ring
  rw [thomInverseRadial_norm_eq, hscalar, smul_smul, one_div, inv_mul_cancel₀, one_smul]
  exact inv_ne_zero hsub

/-- Helper for Definition 23.5.1: the interior inverse-radial/radial composite returns the same
closed-disk subtype representative. -/
theorem radialCompInverseRadialSubtype {b : B} (v : {v : E b // ‖v‖ ≤ 1})
    (hneq : ‖v.1‖ ≠ 1) :
    (⟨(1 / (1 + ‖(((1 - ‖v.1‖)⁻¹ : ℝ) • v.1 : E b)‖)) •
        (((1 - ‖v.1‖)⁻¹ : ℝ) • v.1),
      thomDiskBundleRadialPoint_mem (E := E) b (((1 - ‖v.1‖)⁻¹ : ℝ) • v.1)⟩ :
        {v : E b // ‖v‖ ≤ 1}) = v := by
  -- Hide the single subtype equality behind the already-proved fiber equality.
  apply Subtype.ext
  exact radial_comp_inverseRadial (E := E) v hneq

/-- The quotient map from the closed disk bundle to the Thom space sends the unit sphere locus to
the point at infinity and sends an interior disk point to the corresponding finite fiber point by
inverse radial compactification. -/
noncomputable def thomDiskBundleToThomSpace (x : ThomDiskBundle n E) : ThomSpace n E :=
  if _ : ‖x.1.2‖ = 1 then
    thomSpaceMk n E x.1.proj (OnePoint.infty : OnePoint (E x.1.proj))
  else
    thomSpaceMk n E x.1.proj
      (OnePoint.some (((1 - ‖x.1.2‖)⁻¹ : ℝ) • x.1.2))

/-- The disk-bundle-to-Thom-space map respects the sphere-collapse relation. -/
theorem thomDiskBundleToThomSpace_respects {x y : ThomDiskBundle n E}
    (hxy : x = y ∨ (x ∈ thomSphereLocus n E ∧ y ∈ thomSphereLocus n E)) :
    thomDiskBundleToThomSpace n E x = thomDiskBundleToThomSpace n E y := by
  -- Equal points are trivial, and two boundary points both map to the Thom-space infinity class.
  rcases hxy with rfl | ⟨hx, hy⟩
  · rfl
  · change ‖x.1.2‖ = 1 at hx
    change ‖y.1.2‖ = 1 at hy
    simpa [thomDiskBundleToThomSpace, hx, hy] using
      thomSpaceMk_infty_eq n E x.1.proj y.1.proj

/-- The quotient map `D(E) / S(E) → ThomSpace n E` induced by inverse radial compactification on
the
closed unit disk bundle. -/
noncomputable def thomDiskSphereQuotientToThomSpace :
    ThomDiskSphereQuotient n E → ThomSpace n E :=
  Quotient.lift (thomDiskBundleToThomSpace n E) fun _ _ h ↦
    thomDiskBundleToThomSpace_respects n E h

/-- The fiberwise pointed closed-disk prequotient map sends boundary and infinity points to the
point at infinity in `ThomSpace n E`, and sends interior disk points to their finite Thom-space
classes by inverse radial compactification. -/
noncomputable def thomDiskPreSpaceToThomSpace :
    ThomDiskPreSpace n E → ThomSpace n E
  | ⟨b, x⟩ =>
      x.elim
        (thomSpaceMk n E b (OnePoint.infty : OnePoint (E b)))
        (fun v ↦
          if ‖v.1‖ = 1 then
            thomSpaceMk n E b (OnePoint.infty : OnePoint (E b))
          else
            thomSpaceMk n E b (OnePoint.some (((1 - ‖v.1‖)⁻¹ : ℝ) • v.1)))

/-- Helper for Definition 23.5.1: a pointed disk representative already in the collapsed
boundary-or-infinity class maps to the Thom-space infinity class. -/
theorem thomDiskPreSpaceToThomSpace_eq_infty_of_collapsed {b : B}
    {x : OnePoint {v : E b // ‖v‖ ≤ 1}}
    (hx : x = OnePoint.infty ∨
      ∃ v : {v : E b // ‖v‖ ≤ 1}, x = OnePoint.some v ∧ ‖v.1‖ = 1) :
    thomDiskPreSpaceToThomSpace n E ⟨b, x⟩ =
      thomSpaceMk n E b (OnePoint.infty : OnePoint (E b)) := by
  rcases hx with rfl | ⟨v, rfl, hv⟩
  · -- The added point at infinity maps to the Thom-space infinity class by definition.
    rfl
  · -- Boundary disk points are also sent to the common infinity class.
    simp [thomDiskPreSpaceToThomSpace, hv]

/-- The fiberwise pointed closed-disk prequotient map respects the sphere-and-infinity collapse
relation. -/
theorem thomDiskPreSpaceToThomSpace_respects {x y : ThomDiskPreSpace n E}
    (hxy : thomDiskRel n E x y) :
    thomDiskPreSpaceToThomSpace n E x = thomDiskPreSpaceToThomSpace n E y := by
  -- Equality is immediate, while the collapsed branch sends both representatives to Thom-space
  -- infinity.
  rcases hxy with rfl | ⟨hx, hy⟩
  · rfl
  · calc
      thomDiskPreSpaceToThomSpace n E x =
          thomSpaceMk n E x.1 (OnePoint.infty : OnePoint (E x.1)) :=
        thomDiskPreSpaceToThomSpace_eq_infty_of_collapsed (n := n) (E := E) (b := x.1) hx
      _ =
          thomSpaceMk n E y.1 (OnePoint.infty : OnePoint (E y.1)) :=
        thomSpaceMk_infty_eq n E x.1 y.1
      _ = thomDiskPreSpaceToThomSpace n E y :=
        (thomDiskPreSpaceToThomSpace_eq_infty_of_collapsed (n := n) (E := E) (b := y.1) hy).symm

/-- The map from the auxiliary pointed disk quotient to `ThomSpace n E`. -/
noncomputable def thomDiskQuotientToThomSpace :
    ThomDiskQuotient n E → ThomSpace n E :=
  Quotient.lift (thomDiskPreSpaceToThomSpace n E) fun _ _ h ↦
    thomDiskPreSpaceToThomSpace_respects n E h

/-- A finite fiber point determines a class in the auxiliary pointed disk quotient via radial
compactification into the closed disk bundle. -/
noncomputable def thomSpaceFiniteToThomDiskQuotient (b : B) (v : E b) : ThomDiskQuotient n E :=
  Quotient.mk (thomDiskSetoid n E)
    ⟨b, OnePoint.some ⟨((1 / (1 + ‖v‖)) • v : E b), thomDiskBundleRadialPoint_mem E b v⟩⟩

/-- The pre-Thom-space point corresponding to infinity maps to the distinguished collapsed class,
while a finite fiber point maps to its radial closed-disk representative. -/
noncomputable def thomPreSpaceToThomDiskQuotient :
    Bundle.TotalSpace (OnePoint (Fin n → ℝ)) (ThomFiber E) → ThomDiskQuotient n E
  | ⟨b, x⟩ =>
      x.elim
        (Quotient.mk (thomDiskSetoid n E) ⟨b, OnePoint.infty⟩)
        (fun v ↦ thomSpaceFiniteToThomDiskQuotient n E b v)

/-- The pre-Thom-space-to-disk-quotient map respects the relation identifying all points at
infinity. -/
theorem thomPreSpaceToThomDiskQuotient_respects
    {x y : Bundle.TotalSpace (OnePoint (Fin n → ℝ)) (ThomFiber E)}
    (hxy : thomSpaceRel n E x y) :
    thomPreSpaceToThomDiskQuotient n E x =
      thomPreSpaceToThomDiskQuotient n E y := by
  -- Equal points are trivial, and the infinity branch collapses to the same distinguished class.
  rcases hxy with rfl | ⟨hx, hy⟩
  · rfl
  · have hinfty :
        Quotient.mk (thomDiskSetoid n E) ⟨x.1, (OnePoint.infty : OnePoint {v : E x.1 // ‖v‖ ≤ 1})⟩ =
          Quotient.mk (thomDiskSetoid n E)
            ⟨y.1, (OnePoint.infty : OnePoint {v : E y.1 // ‖v‖ ≤ 1})⟩ := by
      -- Both explicit infinity representatives lie in the collapsed class of `ThomDiskQuotient`.
      exact Quotient.sound <| Or.inr ⟨Or.inl rfl, Or.inl rfl⟩
    simpa [thomPreSpaceToThomDiskQuotient, hx, hy] using hinfty

/-- The inverse-direction map from the Thom space to the auxiliary pointed disk quotient induced by
radial compactification of each fiber. -/
noncomputable def thomSpaceToThomDiskQuotient :
    ThomSpace n E → ThomDiskQuotient n E :=
  Quotient.lift (thomPreSpaceToThomDiskQuotient n E) fun _ _ h ↦
    thomPreSpaceToThomDiskQuotient_respects n E h

/-- The image of the point at infinity in the fiber over `b` is the distinguished collapsed class
in the auxiliary pointed disk quotient. -/
theorem thomSpaceToThomDiskQuotient_infty (b : B) :
    thomSpaceToThomDiskQuotient n E
        (thomSpaceMk n E b (OnePoint.infty : OnePoint (E b))) =
      Quotient.mk (thomDiskSetoid n E) ⟨b, OnePoint.infty⟩ := rfl

/-- Helper for Definition 23.5.1: going from a pointed closed-disk representative to `ThomSpace`
and back returns its class in `ThomDiskQuotient n E`. -/
theorem thomDiskPreSpace_roundTrip (x : ThomDiskPreSpace n E) :
    thomSpaceToThomDiskQuotient n E (thomDiskPreSpaceToThomSpace n E x) =
      Quotient.mk (thomDiskSetoid n E) x := by
  -- Split once into the added infinity point and finite closed-disk representatives.
  rcases x with ⟨b, x⟩
  induction x using OnePoint.rec with
  | infty =>
      -- The explicit infinity representative is already the collapsed basepoint.
      rfl
  | coe v =>
      -- Split the finite closed-disk representative into boundary and interior cases.
      by_cases hv : ‖v.1‖ = 1
      · have hcollapsed :
            Quotient.mk (thomDiskSetoid n E) ⟨b, (OnePoint.infty : OnePoint {w : E b // ‖w‖ ≤ 1})⟩ =
              Quotient.mk (thomDiskSetoid n E) ⟨b, OnePoint.some v⟩ := by
          exact Quotient.sound <| Or.inr ⟨Or.inl rfl, Or.inr ⟨v, rfl, hv⟩⟩
        -- The boundary branch of `thomDiskPreSpaceToThomSpace` lands in the collapsed class.
        simpa [thomSpaceToThomDiskQuotient, thomPreSpaceToThomDiskQuotient,
          thomDiskPreSpaceToThomSpace, hv] using hcollapsed
      · have hmem :
            ‖(((1 + ‖(((1 - ‖v.1‖)⁻¹ : ℝ) • v.1 : E b)‖)⁻¹) •
                (((1 - ‖v.1‖)⁻¹ : ℝ) • v.1) : E b)‖ ≤ 1 := by
          simpa [one_div] using
            thomDiskBundleRadialPoint_mem (E := E) b (((1 - ‖v.1‖)⁻¹ : ℝ) • v.1)
        have hpoint :
            (⟨b, OnePoint.some
                (⟨((1 + ‖(((1 - ‖v.1‖)⁻¹ : ℝ) • v.1 : E b)‖)⁻¹) •
                    (((1 - ‖v.1‖)⁻¹ : ℝ) • v.1),
                  hmem⟩ :
                  {w : E b // ‖w‖ ≤ 1})⟩ : ThomDiskPreSpace n E) =
              ⟨b, OnePoint.some v⟩ := by
          -- Collapse the interior branch to equality using the subtype round-trip helper.
          simpa [one_div] using congrArg (fun w : {w : E b // ‖w‖ ≤ 1} ↦
            (⟨b, OnePoint.some w⟩ : ThomDiskPreSpace n E))
            (radialCompInverseRadialSubtype (E := E) v hv)
        -- With the representative normalized, the quotient class is unchanged.
        simpa [thomSpaceToThomDiskQuotient, thomPreSpaceToThomDiskQuotient,
          thomDiskPreSpaceToThomSpace, thomSpaceFiniteToThomDiskQuotient, hv, one_div] using
          Quotient.sound (Or.inl hpoint)

/-- Helper for Definition 23.5.1: going from a Thom-space representative to the pointed closed
disk quotient and back returns its class in `ThomSpace n E`. -/
theorem thomPreSpace_roundTrip (x : Bundle.TotalSpace (OnePoint (Fin n → ℝ)) (ThomFiber E)) :
    thomDiskQuotientToThomSpace n E (thomPreSpaceToThomDiskQuotient n E x) =
      Quotient.mk (thomSpaceSetoid n E) x := by
  -- Split once into the infinity point and finite fiber points of `ThomSpace`.
  rcases x with ⟨b, x⟩
  induction x using OnePoint.rec with
  | infty =>
      -- The infinity representative stays in the collapsed Thom-space class.
      rfl
  | coe v =>
      have hneq : ‖((1 / (1 + ‖v‖)) • v : E b)‖ ≠ 1 := by
        exact thomRadial_norm_ne_one (E := E) b v
      have hneq' : ‖(((1 + ‖v‖)⁻¹ : ℝ) • v : E b)‖ ≠ 1 := by
        simpa [one_div] using hneq
      -- The finite branch stays away from the boundary, so inverse radial undoing is exact.
      have hpoint :
          (⟨b,
              OnePoint.some
                (((1 - ‖((1 / (1 + ‖v‖)) • v : E b)‖)⁻¹ : ℝ) •
                  ((1 / (1 + ‖v‖)) • v))⟩ : ThomPreSpace n E) =
            ⟨b, OnePoint.some v⟩ := by
        -- The underlying fiber vector is exactly restored by `inverseRadial_comp_radial`.
        simpa [one_div] using congrArg (fun w : E b ↦ (⟨b, OnePoint.some w⟩ : ThomPreSpace n E))
          (inverseRadial_comp_radial (E := E) b v)
      have hrel :
          thomSpaceRel n E
            (⟨b,
                OnePoint.some
                  (((1 - ‖((1 / (1 + ‖v‖)) • v : E b)‖)⁻¹ : ℝ) •
                    ((1 / (1 + ‖v‖)) • v))⟩ : ThomPreSpace n E)
            ⟨b, OnePoint.some v⟩ := Or.inl hpoint
      simpa [thomDiskQuotientToThomSpace, thomPreSpaceToThomDiskQuotient,
        thomDiskPreSpaceToThomSpace, thomSpaceFiniteToThomDiskQuotient, hneq', one_div] using
        (Quotient.sound hrel :
          Quotient.mk (thomSpaceSetoid n E)
              (⟨b,
                  OnePoint.some
                    (((1 - ‖((1 / (1 + ‖v‖)) • v : E b)‖)⁻¹ : ℝ) •
                      ((1 / (1 + ‖v‖)) • v))⟩ : ThomPreSpace n E) =
            Quotient.mk (thomSpaceSetoid n E) ⟨b, OnePoint.some v⟩)

/-- Definition 23.5.1 (2). The rank-`n` auxiliary pointed closed-disk quotient
`ThomDiskQuotient n E`, obtained from the closed disk bundle by also collapsing the added
fiberwise points at infinity, is equivalent to `ThomSpace n E`. This is the uniform metric
disk model of the Thom space in every rank, including the rank-`0` edge case. -/
noncomputable def thomDiskQuotientEquivThomSpace :
    ThomDiskQuotient n E ≃ ThomSpace n E where
  toFun := thomDiskQuotientToThomSpace n E
  invFun := thomSpaceToThomDiskQuotient n E
  left_inv := by
    -- The pointed prequotient round trip is exactly the left inverse on quotient classes.
    intro x
    refine Quotient.inductionOn x ?_
    intro y
    simpa [thomDiskQuotientToThomSpace, thomSpaceToThomDiskQuotient] using
      thomDiskPreSpace_roundTrip (n := n) (E := E) y
  right_inv := by
    -- The Thom-space prequotient round trip is exactly the right inverse on quotient classes.
    intro x
    refine Quotient.inductionOn x ?_
    intro y
    simpa [thomDiskQuotientToThomSpace, thomSpaceToThomDiskQuotient] using
      thomPreSpace_roundTrip (n := n) (E := E) y

/-- The forward map of the Thom-space equivalence associated to the pointed disk quotient is the
quotient-to-Thom comparison map. -/
theorem thomDiskQuotientEquivThomSpace_toFun :
    (thomDiskQuotientEquivThomSpace n E).toFun =
      thomDiskQuotientToThomSpace n E := rfl

/-- The Thom-space equivalence associated to the pointed disk quotient acts by the quotient-to-Thom
comparison map. -/
@[simp] theorem thomDiskQuotientEquivThomSpace_apply (x : ThomDiskQuotient n E) :
    thomDiskQuotientEquivThomSpace n E x =
      thomDiskQuotientToThomSpace n E x := rfl

/-- The inverse of the Thom-space equivalence associated to the pointed disk quotient acts by the
Thom-space-to-quotient comparison map. -/
@[simp] theorem thomDiskQuotientEquivThomSpace_symm_apply (x : ThomSpace n E) :
    (thomDiskQuotientEquivThomSpace n E).symm x =
      thomSpaceToThomDiskQuotient n E x := rfl

/-- The map from the auxiliary pointed disk quotient to `ThomSpace n E` is bijective. -/
theorem thomDiskQuotientToThomSpace_bijective :
    Function.Bijective (thomDiskQuotientToThomSpace n E) := by
  -- The comparison map is the forward map of the constructed equivalence.
  simpa using (thomDiskQuotientEquivThomSpace n E).bijective

section SphereModel

variable [TopologicalSpace B]
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
variable [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
variable [VectorBundle ℝ (Fin n → ℝ) E]

/-- The pointed closed-disk prequotient maps to the literal disk/sphere quotient by forgetting the
added point at infinity and sending it to the collapsed sphere class. -/
noncomputable def thomDiskPreSpaceToThomDiskSphereQuotient (hn : 0 < n) :
    ThomDiskPreSpace n E → ThomDiskSphereQuotient n E
  | ⟨b, x⟩ =>
      x.elim
        (Quotient.mk (thomDiskBundleSetoid n E) (thomSphereBundlePoint n E hn b))
        (fun v ↦ Quotient.mk (thomDiskBundleSetoid n E) ⟨⟨b, v.1⟩, v.2⟩)

-- The next helper isolates the common sphere class used in the disk/sphere quotient-respect proof.
/-- Helper for Definition 23.5.1: a pointed closed-disk representative in the collapsed
boundary-or-infinity class maps to the common sphere class in `D(E) / S(E)`. -/
theorem thomDiskPreSpaceToThomDiskSphereQuotient_eq_spherePoint_of_collapsed (hn : 0 < n)
    {b : B} {x : OnePoint {v : E b // ‖v‖ ≤ 1}}
    (hx : x = OnePoint.infty ∨
      ∃ v : {v : E b // ‖v‖ ≤ 1}, x = OnePoint.some v ∧ ‖v.1‖ = 1) :
    thomDiskPreSpaceToThomDiskSphereQuotient n E hn ⟨b, x⟩ =
      Quotient.mk (thomDiskBundleSetoid n E) (thomSphereBundlePoint n E hn b) := by
  rcases hx with rfl | ⟨v, rfl, hv⟩
  · -- The added point at infinity is sent to the chosen sphere basepoint by definition.
    rfl
  · -- Any boundary point is identified with the chosen sphere point in the disk/sphere quotient.
    apply Quotient.sound
    right
    refine ⟨?_, thomSphereBundlePoint_mem_locus n E hn b⟩
    simpa [thomSphereLocus] using hv

theorem thomDiskPreSpaceToThomDiskSphereQuotient_respects (hn : 0 < n)
    {x y : ThomDiskPreSpace n E} (hxy : thomDiskRel n E x y) :
    thomDiskPreSpaceToThomDiskSphereQuotient n E hn x =
      thomDiskPreSpaceToThomDiskSphereQuotient n E hn y := by
  -- Equality is immediate, and the collapsed branch sends both sides to the common sphere class.
  rcases hxy with rfl | ⟨hx, hy⟩
  · rfl
  · have hsphere :
        Quotient.mk (thomDiskBundleSetoid n E) (thomSphereBundlePoint n E hn x.1) =
          Quotient.mk (thomDiskBundleSetoid n E) (thomSphereBundlePoint n E hn y.1) := by
      -- Chosen sphere points over different base points are still in the collapsed sphere class.
      exact Quotient.sound <|
        Or.inr
          ⟨thomSphereBundlePoint_mem_locus n E hn x.1,
            thomSphereBundlePoint_mem_locus n E hn y.1⟩
    calc
      thomDiskPreSpaceToThomDiskSphereQuotient n E hn x =
          Quotient.mk (thomDiskBundleSetoid n E) (thomSphereBundlePoint n E hn x.1) :=
        thomDiskPreSpaceToThomDiskSphereQuotient_eq_spherePoint_of_collapsed
          (n := n) (E := E) hn (b := x.1) hx
      _ =
          Quotient.mk (thomDiskBundleSetoid n E) (thomSphereBundlePoint n E hn y.1) :=
        hsphere
      _ = thomDiskPreSpaceToThomDiskSphereQuotient n E hn y :=
        (thomDiskPreSpaceToThomDiskSphereQuotient_eq_spherePoint_of_collapsed
          (n := n) (E := E) hn (b := y.1) hy).symm

/-- The quotient map from the auxiliary pointed disk quotient to the literal disk/sphere quotient.
In positive rank the extra points at infinity are sent to the collapsed sphere class. -/
noncomputable def thomDiskQuotientToThomDiskSphereQuotient (hn : 0 < n) :
    ThomDiskQuotient n E → ThomDiskSphereQuotient n E :=
  Quotient.lift (thomDiskPreSpaceToThomDiskSphereQuotient n E hn) fun _ _ h ↦
    thomDiskPreSpaceToThomDiskSphereQuotient_respects n E hn h

/-- The inverse-direction map from `ThomSpace n E` to the literal disk/sphere quotient factors
through the auxiliary pointed disk quotient. -/
noncomputable def thomSpaceToThomDiskSphereQuotient (hn : 0 < n) :
    ThomSpace n E → ThomDiskSphereQuotient n E :=
  thomDiskQuotientToThomDiskSphereQuotient n E hn ∘ thomSpaceToThomDiskQuotient n E

/-- Helper for Definition 23.5.1: passing from the auxiliary pointed disk quotient to the literal
disk/sphere quotient and then to `ThomSpace n E` agrees with the direct comparison map. -/
theorem thomDiskSphereQuotientToThomSpace_comp_thomDiskQuotientToThomDiskSphereQuotient
    (hn : 0 < n) (x : ThomDiskQuotient n E) :
    thomDiskSphereQuotientToThomSpace n E
        (thomDiskQuotientToThomDiskSphereQuotient n E hn x) =
      thomDiskQuotientToThomSpace n E x := by
  -- Quotient induction reduces the comparison to the prequotient formulas.
  refine Quotient.inductionOn x ?_
  intro y
  rcases y with ⟨b, y⟩
  induction y using OnePoint.rec with
  | infty =>
      -- The auxiliary infinity point is sent to the chosen sphere class, which maps back to Thom
      -- infinity because the chosen vector has norm `1`.
      simp [thomDiskQuotientToThomDiskSphereQuotient, thomDiskSphereQuotientToThomSpace,
        thomDiskPreSpaceToThomDiskSphereQuotient, thomDiskQuotientToThomSpace,
        thomDiskPreSpaceToThomSpace, thomDiskBundleToThomSpace, thomSphereBundlePoint,
        thomSphereVector_norm]
  | coe v =>
      -- Finite closed-disk representatives are unchanged by the comparison through the literal
      -- disk/sphere quotient.
      rfl

/-- In positive rank, the literal disk/sphere quotient `ThomDiskSphereQuotient n E = D(E) / S(E)`
is equivalent to `ThomSpace n E`. The inverse is given by first passing to the auxiliary pointed
disk quotient and then forgetting the added points at infinity. -/
noncomputable def thomDiskSphereQuotientEquivThomSpace (hn : 0 < n) :
    ThomDiskSphereQuotient n E ≃ ThomSpace n E where
  toFun := thomDiskSphereQuotientToThomSpace n E
  invFun := thomSpaceToThomDiskSphereQuotient n E hn
  left_inv := by
    -- Factor the inverse through the pointed quotient, then use its round trip on a chosen
    -- pointed representative of the disk-bundle point.
    intro x
    refine Quotient.inductionOn x ?_
    intro y
    have hround :=
      congrArg (thomDiskQuotientToThomDiskSphereQuotient n E hn)
        (thomDiskPreSpace_roundTrip (n := n) (E := E)
          ⟨y.1.proj, OnePoint.some ⟨y.1.2, y.2⟩⟩)
    simpa [thomSpaceToThomDiskSphereQuotient, thomDiskSphereQuotientToThomSpace,
      thomDiskQuotientToThomDiskSphereQuotient, thomDiskPreSpaceToThomDiskSphereQuotient,
      thomDiskBundleToThomSpace, thomDiskPreSpaceToThomSpace] using
      hround
  right_inv := by
    -- Route correction: compare through `ThomDiskQuotient`, then invoke the all-ranks equivalence.
    intro x
    calc
      thomDiskSphereQuotientToThomSpace n E (thomSpaceToThomDiskSphereQuotient n E hn x) =
          thomDiskQuotientToThomSpace n E (thomSpaceToThomDiskQuotient n E x) := by
        simpa [thomSpaceToThomDiskSphereQuotient] using
          thomDiskSphereQuotientToThomSpace_comp_thomDiskQuotientToThomDiskSphereQuotient
            (n := n) (E := E) hn (thomSpaceToThomDiskQuotient n E x)
      _ = x := (thomDiskQuotientEquivThomSpace n E).right_inv x

/-- The topology on `ThomSpace n E` is transported from the disk/sphere quotient model via
`thomDiskSphereQuotientToThomSpace`. -/
noncomputable instance : TopologicalSpace (ThomSpace n E) :=
  TopologicalSpace.coinduced (thomDiskSphereQuotientToThomSpace n E) inferInstance

/-- Companion to Definition 23.5.1 (2). After choosing a fiberwise metric and assuming `0 < n`,
the literal disk/sphere quotient `ThomDiskSphereQuotient n E = D(E) / S(E)` is homeomorphic to
`ThomSpace n E`. This recovers the usual positive-rank disk/sphere model from the uniform pointed
disk quotient. -/
noncomputable def thomDiskSphereQuotientHomeomorphThomSpace (hn : 0 < n)
    (hnorm : Continuous fun x : Bundle.TotalSpace (Fin n → ℝ) E ↦ ‖x.2‖) :
    ThomDiskSphereQuotient n E ≃ₜ ThomSpace n E where
  toEquiv := thomDiskSphereQuotientEquivThomSpace n E hn
  continuous_toFun := by
    let _ := hnorm
    simpa using
      (continuous_coinduced_rng : Continuous (thomDiskSphereQuotientToThomSpace n E))
  continuous_invFun := by
    let _ := hnorm
    rw [continuous_coinduced_dom]
    have hleft :
        ((thomDiskSphereQuotientEquivThomSpace n E hn).symm ∘
          thomDiskSphereQuotientToThomSpace n E) = id := by
      funext x
      exact (thomDiskSphereQuotientEquivThomSpace n E hn).left_inv x
    simpa [hleft] using
      (continuous_id : Continuous (id : ThomDiskSphereQuotient n E → ThomDiskSphereQuotient n E))

/-- The map `thomDiskSphereQuotientToThomSpace` is a homeomorphism when `0 < n`. -/
theorem thomDiskSphereQuotientToThomSpace_isHomeomorph (hn : 0 < n)
    (hnorm : Continuous fun x : Bundle.TotalSpace (Fin n → ℝ) E ↦ ‖x.2‖) :
    IsHomeomorph (thomDiskSphereQuotientToThomSpace n E) :=
  (thomDiskSphereQuotientHomeomorphThomSpace (n := n) (E := E) hn hnorm).isHomeomorph

/-- The forward map of the homeomorphism `thomDiskSphereQuotientHomeomorphThomSpace` is the
quotient-to-Thom comparison map. -/
theorem thomDiskSphereQuotientHomeomorphThomSpace_toFun (hn : 0 < n)
    (hnorm : Continuous fun x : Bundle.TotalSpace (Fin n → ℝ) E ↦ ‖x.2‖) :
    (thomDiskSphereQuotientHomeomorphThomSpace (n := n) (E := E) hn hnorm).toFun =
      thomDiskSphereQuotientToThomSpace n E := rfl

/-- The homeomorphism `thomDiskSphereQuotientHomeomorphThomSpace` acts by
`thomDiskSphereQuotientToThomSpace`. -/
@[simp] theorem thomDiskSphereQuotientHomeomorphThomSpace_apply (hn : 0 < n)
    (hnorm : Continuous fun x : Bundle.TotalSpace (Fin n → ℝ) E ↦ ‖x.2‖)
    (x : ThomDiskSphereQuotient n E) :
    thomDiskSphereQuotientHomeomorphThomSpace (n := n) (E := E) hn hnorm x =
      thomDiskSphereQuotientToThomSpace n E x := rfl

/-- The quotient map `D(E) / S(E) → ThomSpace n E` is bijective as a map of types. -/
theorem thomDiskSphereQuotientToThomSpace_bijective (hn : 0 < n) :
    Function.Bijective (thomDiskSphereQuotientToThomSpace n E) := by
  simpa [thomDiskSphereQuotientEquivThomSpace] using
    (thomDiskSphereQuotientEquivThomSpace n E hn).bijective

/-- The forward map of the literal disk/sphere quotient comparison is
`thomDiskSphereQuotientToThomSpace`. -/
theorem thomDiskSphereQuotientEquivThomSpace_toFun (hn : 0 < n) :
    (thomDiskSphereQuotientEquivThomSpace n E hn).toFun =
      thomDiskSphereQuotientToThomSpace n E := rfl

/-- The literal disk/sphere quotient comparison acts by
`thomDiskSphereQuotientToThomSpace`. -/
@[simp] theorem thomDiskSphereQuotientEquivThomSpace_apply (hn : 0 < n)
    (x : ThomDiskSphereQuotient n E) :
    thomDiskSphereQuotientEquivThomSpace n E hn x =
      thomDiskSphereQuotientToThomSpace n E x := rfl

end SphereModel

end
