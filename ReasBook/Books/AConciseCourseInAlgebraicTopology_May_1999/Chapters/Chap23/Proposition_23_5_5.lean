import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Data.ZMod.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Proposition_23_5_5.ThomClassOwner

noncomputable section

universe u

-- Route correction: `Definition_23_5_3` is still broken in this workspace, so this item imports
-- the theorem-local Thom-class owner from `Proposition_23_5_5/ThomClassOwner`. The proof below
-- is unchanged mathematically: it only uses the abstract Thom-space cohomology module together
-- with the supplied fiber-restriction maps and the fiberwise `ZMod 2` identifications.

section

variable {B : Type u} {n : ℕ} {E : B → Type u}
variable [TopologicalSpace B]
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
variable [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
variable [VectorBundle ℝ (Fin n → ℝ) E]
variable (H : ℤ → (X : TopCat.{u}) → Set X → Type)
variable [∀ q (X : TopCat.{u}) (A : Set X), AddCommGroup (H q X A)]
variable [∀ q (X : TopCat.{u}) (A : Set X), Module (ZMod 2) (H q X A)]

/-- Helper for Proposition 23.5.5: the only nonzero element of `ZMod 2` is `1`. -/
private theorem zmodTwo_eq_one_of_ne_zero (z : ZMod 2) (hz : z ≠ 0) : z = 1 := by
  -- Convert nonvanishing into a statement about the canonical natural-number representative.
  have hzval0 : z.val ≠ 0 := by
    intro hzval
    apply hz
    exact (ZMod.val_eq_zero z).mp hzval
  have hzle : z.val ≤ 1 := Nat.lt_succ_iff.mp (ZMod.val_lt z)
  have hzge : 1 ≤ z.val := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hzval0)
  have hzval1 : z.val = 1 := le_antisymm hzle hzge
  exact (ZMod.val_eq_one (by decide : 1 < 2) z).mp hzval1

/-- Helper for Proposition 23.5.5: a nonzero vector in a `ZMod 2`-line is the unique nonzero
class under any linear equivalence with `ZMod 2`. -/
private theorem linearEquivZModTwo_eq_one_of_ne_zero
    {M : Type u} [AddCommGroup M] [Module (ZMod 2) M]
    (e : M ≃ₗ[ZMod 2] ZMod 2) (x : M) (hx : x ≠ 0) :
    e x = 1 := by
  -- Transfer nonvanishing across the equivalence and reduce to `ZMod 2`.
  have hx0 : e x ≠ 0 := by
    intro h0
    apply hx
    exact e.injective (by simpa using h0)
  exact zmodTwo_eq_one_of_ne_zero (e x) hx0

/-- Helper for Proposition 23.5.5: any nonzero vector in a `ZMod 2`-line generates the whole
module. -/
private theorem existsSmulEq_of_neZero_of_linearEquivZModTwo
    {M : Type u} [AddCommGroup M] [Module (ZMod 2) M]
    (e : M ≃ₗ[ZMod 2] ZMod 2) (y : M) (hy : y ≠ 0) (x : M) :
    ∃ r : ZMod 2, r • y = x := by
  -- Choose the scalar corresponding to `x` under the linear equivalence.
  refine ⟨e x, ?_⟩
  apply e.injective
  -- Once `e y = 1`, scalar multiplication in the target becomes tautological.
  calc
    e ((e x) • y) = (e x) • e y := by rw [e.map_smul]
    _ = e x := by simp [linearEquivZModTwo_eq_one_of_ne_zero e y hy]

/-- Helper for Proposition 23.5.5: a `ZMod 2`-line has only one nonzero element. -/
private theorem eq_of_neZero_of_linearEquivZModTwo
    {M : Type u} [AddCommGroup M] [Module (ZMod 2) M]
    (e : M ≃ₗ[ZMod 2] ZMod 2) (x y : M) (hx : x ≠ 0) (hy : y ≠ 0) :
    x = y := by
  -- Compare both vectors after transporting them to `ZMod 2`.
  apply e.injective
  rw [linearEquivZModTwo_eq_one_of_ne_zero e x hx,
    linearEquivZModTwo_eq_one_of_ne_zero e y hy]

omit [TopologicalSpace B] [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
  [FiberBundle (Fin n → ℝ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [VectorBundle ℝ (Fin n → ℝ) E] in
/-- Helper for Proposition 23.5.5: every Thom class restricts nontrivially on each fiber once
that fiber is identified with `ZMod 2`. -/
private theorem thomClassRestriction_neZero
    {fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[ZMod 2]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))}
    (μ : ThomClass H fiberRestriction)
    (b : B)
    (e_b :
      reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b)) ≃ₗ[ZMod 2] ZMod 2) :
    (fiberRestriction b) μ ≠ 0 := by
  -- Use the generator property against the chosen nonzero class `e_b.symm 1`.
  have hnonzero : e_b.symm 1 ≠ 0 := by
    intro hzero
    have honeZero : (1 : ZMod 2) = 0 := by
      simpa using congrArg e_b hzero
    exact one_ne_zero honeZero
  rcases ThomClass.exists_smul_eq (H := H) μ b (e_b.symm 1) with ⟨r, hr⟩
  intro hzero
  have hfiberZero : e_b.symm 1 = 0 := by
    calc
      e_b.symm 1 = r • (fiberRestriction b) μ := hr.symm
      _ = 0 := by simp [hzero]
  exact hnonzero hfiberZero

omit [TopologicalSpace B] [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
  [FiberBundle (Fin n → ℝ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [VectorBundle ℝ (Fin n → ℝ) E] in
/-- Helper for Proposition 23.5.5: two Thom classes are equal once their underlying reduced
cohomology classes agree. -/
private theorem thomClass_eq_of_toReducedCohomology_eq
    {fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[ZMod 2]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b))}
    {μ μ' : ThomClass H fiberRestriction}
    (h : μ.toReducedCohomology = μ'.toReducedCohomology) :
    μ = μ' := by
  -- The remaining field is propositional, so proof irrelevance finishes the structure equality.
  cases μ with
  | mk toμ hμ =>
    cases μ' with
    | mk toμ' hμ' =>
      dsimp at h
      cases h
      have hProof : hμ = hμ' := Subsingleton.elim _ _
      cases hProof
      rfl

omit [TopologicalSpace B] [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
  [FiberBundle (Fin n → ℝ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [VectorBundle ℝ (Fin n → ℝ) E] in
private theorem real_vector_bundle_unique_modTwo_thomClass_of_nonempty
    [Nonempty B]
    (fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[ZMod 2]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b)))
    (hFiberRestrictionBijective : ∀ b : B, Function.Bijective (fiberRestriction b))
    (hFiberCohomology :
      ∀ b : B,
        Nonempty
          (reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b)) ≃ₗ[ZMod 2] ZMod 2)) :
    ∃ μ : ThomClass H fiberRestriction, ∀ μ' : ThomClass H fiberRestriction, μ' = μ := by
  -- Use a chosen base fiber to lift the unique nonzero class back to Thom cohomology.
  obtain ⟨b0⟩ := ‹Nonempty B›
  obtain ⟨e0⟩ := hFiberCohomology b0
  let x0 : reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b0)) := e0.symm 1
  have hx0 : x0 ≠ 0 := by
    intro hzero
    have honeZero : (1 : ZMod 2) = 0 := by
      simpa [x0] using congrArg e0 hzero
    exact one_ne_zero honeZero
  obtain ⟨u, hu_spec⟩ := (hFiberRestrictionBijective b0).2 x0
  have hu_ne_zero : u ≠ 0 := by
    intro hzero
    apply hx0
    simpa [hzero] using hu_spec.symm
  -- Injectivity on each fiber propagates that nonvanishing to every restriction.
  have huRestrictionNonzero :
      ∀ b : B, (fiberRestriction b) u ≠ 0 := by
    intro b hzero
    apply hu_ne_zero
    exact (hFiberRestrictionBijective b).1 (by simp [hzero])
  have hGenerates :
      ∀ b : B,
        ∀ x : reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b)),
          ∃ r : ZMod 2, r • ((fiberRestriction b) u) = x := by
    intro b x
    obtain ⟨e_b⟩ := hFiberCohomology b
    exact existsSmulEq_of_neZero_of_linearEquivZModTwo e_b ((fiberRestriction b) u)
      (huRestrictionNonzero b) x
  -- Package the lifted class as the candidate Thom class.
  let μ : ThomClass H fiberRestriction :=
    { toReducedCohomology := u
      restricts_to_generator := hGenerates }
  refine ⟨μ, ?_⟩
  intro μ'
  -- Any other Thom class has the same nonzero restriction on the chosen fiber.
  have hμ'Nonzero : (fiberRestriction b0) μ' ≠ 0 := by
    exact thomClassRestriction_neZero (H := H) μ' b0 e0
  have hμNonzero : (fiberRestriction b0) μ ≠ 0 := by
    simpa [μ] using huRestrictionNonzero b0
  have hRestrictionEq : (fiberRestriction b0) μ' = (fiberRestriction b0) μ := by
    exact eq_of_neZero_of_linearEquivZModTwo e0 _ _ hμ'Nonzero hμNonzero
  have hUnderlying : μ'.toReducedCohomology = μ.toReducedCohomology := by
    apply (hFiberRestrictionBijective b0).1
    simpa using hRestrictionEq
  exact thomClass_eq_of_toReducedCohomology_eq (H := H) hUnderlying

omit [TopologicalSpace B] [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
  [FiberBundle (Fin n → ℝ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [VectorBundle ℝ (Fin n → ℝ) E] in
/-- Proposition 23.5.5. For coefficients in `ZMod 2`, a real vector bundle has a unique Thom
class, hence a unique `ZMod 2` orientation in the sense of Definition 23.5.3, provided the base
has a fiber on which the generator condition can be tested. -/
theorem real_vector_bundle_unique_modTwo_thomClass
    [Nonempty B]
    (fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[ZMod 2]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b)))
    (hFiberRestrictionBijective : ∀ b : B, Function.Bijective (fiberRestriction b))
    (hFiberCohomology :
      ∀ b : B,
        Nonempty
          (reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b)) ≃ₗ[ZMod 2] ZMod 2)) :
    ∃ μ : ThomClass H fiberRestriction, ∀ μ' : ThomClass H fiberRestriction, μ' = μ := by
  exact real_vector_bundle_unique_modTwo_thomClass_of_nonempty
    H fiberRestriction hFiberRestrictionBijective hFiberCohomology

/-- On a nonempty base, Proposition 23.5.5 makes `ThomClass H fiberRestriction` a subsingleton
for `ZMod 2` coefficients. -/
instance real_vector_bundle_modTwo_thomClass_subsingleton
    [Nonempty B]
    (fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[ZMod 2]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b)))
    (hFiberRestrictionBijective : ∀ b : B, Function.Bijective (fiberRestriction b))
    (hFiberCohomology :
      ∀ b : B,
        Nonempty
          (reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b)) ≃ₗ[ZMod 2] ZMod 2)) :
    Subsingleton (ThomClass H fiberRestriction) where
  allEq μ μ' := by
    rcases real_vector_bundle_unique_modTwo_thomClass
        H fiberRestriction hFiberRestrictionBijective hFiberCohomology with ⟨μ₀, hμ₀⟩
    exact (hμ₀ μ).trans (hμ₀ μ').symm

omit [TopologicalSpace B] [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
  [FiberBundle (Fin n → ℝ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [VectorBundle ℝ (Fin n → ℝ) E] in
/-- Proposition 23.5.5 determines any two mod-`2` Thom classes with the chosen fiber-restriction
maps to be equal. -/
theorem real_vector_bundle_modTwo_thomClass_eq
    [Nonempty B]
    (fiberRestriction :
      ∀ b : B,
        thomReducedCohomology n E H (n : ℤ) →ₗ[ZMod 2]
          reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b)))
    (hFiberRestrictionBijective : ∀ b : B, Function.Bijective (fiberRestriction b))
    (hFiberCohomology :
      ∀ b : B,
        Nonempty
          (reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b)) ≃ₗ[ZMod 2] ZMod 2))
    (μ μ' : ThomClass H fiberRestriction) :
    μ = μ' := by
  exact
    (real_vector_bundle_modTwo_thomClass_subsingleton
      H fiberRestriction hFiberRestrictionBijective hFiberCohomology).allEq μ μ'

end
