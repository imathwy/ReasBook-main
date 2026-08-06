import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Homology.ShortComplex.Ab

open scoped DirectSum
open CategoryTheory

universe u

-- The source-facing data here are the telescope map on `⨁ i, A i` and the canonical map to the
-- sequential direct limit. The public statement uses the canonical `ShortComplex`/`Ab` owners
-- from mathlib rather than encoding abelian groups as `ℤ`-modules on the public surface.

variable {A : ℕ → Type u} [∀ i, AddCommGroup (A i)]

/-- The iterated transition map `A m → A n` obtained by composing the successor maps in the
sequence `A₀ ⟶ A₁ ⟶ A₂ ⟶ ⋯`. -/
def abelianSequenceMap (f : ∀ i : ℕ, A i →+ A (i + 1)) (m n : ℕ) (h : m ≤ n) : A m →+ A n :=
  Nat.leRecOn h
    (fun {i} g ↦ (f i).comp g)
    (AddMonoidHom.id _)

/-- The iterated transition maps attached to a sequence of abelian groups form a directed system. -/
instance abelianSequenceDirectedSystem (f : ∀ i : ℕ, A i →+ A (i + 1)) :
    DirectedSystem A (abelianSequenceMap f · · ·) :=
by
  refine ⟨?_, ?_⟩
  · -- The iterated map over a trivial interval is the identity.
    intro i x
    simpa [abelianSequenceMap] using
      congrArg (fun g : A i →+ A i ↦ g x)
        (Nat.leRecOn_self (next := fun {k} g ↦ (f k).comp g) (AddMonoidHom.id (A i)))
  · -- Concatenating two iterated transition maps agrees with iterating over the composite interval.
    intro k j i hij hjk x
    induction k, hjk using Nat.le_induction with
    | base =>
        have hid : abelianSequenceMap f j j le_rfl = AddMonoidHom.id (A j) := by
          simpa [abelianSequenceMap] using
            (Nat.leRecOn_self (next := fun {n} g ↦ (f n).comp g) (AddMonoidHom.id (A j)))
        rw [hid]
        simp
    | succ k hjk ih =>
        have hleft :
            abelianSequenceMap f j (k + 1) (Nat.le_trans hjk (Nat.le_succ k))
                ((abelianSequenceMap f i j hij) x) =
              f k (abelianSequenceMap f j k hjk ((abelianSequenceMap f i j hij) x)) := by
          simpa [abelianSequenceMap] using
            congrArg (fun g : A j →+ A (k + 1) ↦ g ((abelianSequenceMap f i j hij) x))
              (Nat.leRecOn_succ (h1 := hjk) (h2 := Nat.le_trans hjk (Nat.le_succ k))
                (next := fun {n} g ↦ (f n).comp g) (AddMonoidHom.id (A j)))
        have hright :
            abelianSequenceMap f i (k + 1) (Nat.le_trans (hij.trans hjk) (Nat.le_succ k)) x =
              f k (abelianSequenceMap f i k (hij.trans hjk) x) := by
          simpa [abelianSequenceMap] using
            congrArg (fun g : A i →+ A (k + 1) ↦ g x)
              (Nat.leRecOn_succ (h1 := hij.trans hjk)
                (h2 := Nat.le_trans (hij.trans hjk) (Nat.le_succ k))
                (next := fun {n} g ↦ (f n).comp g) (AddMonoidHom.id (A i)))
        rw [hleft, hright]
        exact congrArg (f k) ih

/-- The telescope map on `⨁ i, A i` whose cokernel computes the sequential colimit. -/
noncomputable def abelianSequenceTelescopeMap (f : ∀ i : ℕ, A i →+ A (i + 1)) :
    (⨁ i : ℕ, A i) →+ ⨁ i : ℕ, A i :=
  DirectSum.toAddMonoid fun i ↦
    DirectSum.of A i - (DirectSum.of A (i + 1)).comp (f i)

/-- The canonical map from the direct sum of the terms of a sequence to its sequential colimit. -/
noncomputable def abelianSequenceColimitMap (f : ∀ i : ℕ, A i →+ A (i + 1)) :
    (⨁ i : ℕ, A i) →+ AddCommGroup.DirectLimit A (abelianSequenceMap f) :=
  DirectSum.toAddMonoid fun i ↦
    AddCommGroup.DirectLimit.of A (abelianSequenceMap f) i

/-- Helper for Lemma 14.6.2: extending the upper index by one applies the next transition map. -/
lemma abelianSequenceMap_step (f : ∀ i : ℕ, A i →+ A (i + 1)) {i j : ℕ} (hij : i ≤ j)
    (x : A i) :
    abelianSequenceMap f i (j + 1) (Nat.le_trans hij (Nat.le_succ j)) x =
      f j (abelianSequenceMap f i j hij x) := by
  simpa [abelianSequenceMap] using
    congrArg (fun g : A i →+ A (j + 1) ↦ g x)
      (Nat.leRecOn_succ (h1 := hij) (h2 := Nat.le_trans hij (Nat.le_succ j))
        (next := fun {k} g ↦ (f k).comp g) (AddMonoidHom.id (A i)))

/-- Helper for Lemma 14.6.2: the iterated transition map over one successor step is `f i`. -/
lemma abelianSequenceMap_succ (f : ∀ i : ℕ, A i →+ A (i + 1)) (i : ℕ) (x : A i) :
    abelianSequenceMap f i (i + 1) (Nat.le_succ i) x = f i x := by
  rw [abelianSequenceMap_step f (hij := le_rfl)]
  rw [DirectedSystem.map_self (f := (abelianSequenceMap f · · ·)) x]

/-- The canonical map to the sequential colimit kills the telescope relations. -/
theorem abelianSequenceColimitMap_comp_telescopeMap (f : ∀ i : ℕ, A i →+ A (i + 1)) :
    (abelianSequenceColimitMap f).comp (abelianSequenceTelescopeMap f) = 0 :=
by
  -- It is enough to check the relation on the direct-sum generators.
  apply DirectSum.addHom_ext
  intro i x
  -- On a generator, the two summands become equal in the direct limit.
  simpa [abelianSequenceColimitMap, abelianSequenceTelescopeMap, AddMonoidHom.comp_apply,
    abelianSequenceMap_succ] using
    sub_eq_zero.mpr
      ((AddCommGroup.DirectLimit.of_f (G := A) (f := abelianSequenceMap f) (Nat.le_succ i) x).symm)

/-- Helper for Lemma 14.6.2: the telescope relation also vanishes after bundling the maps in
`Ab`. -/
theorem abelianSequenceColimitMap_comp_telescopeMap_hom (f : ∀ i : ℕ, A i →+ A (i + 1)) :
    AddCommGrpCat.ofHom (abelianSequenceTelescopeMap f) ≫
        AddCommGrpCat.ofHom (abelianSequenceColimitMap f) = 0 := by
  -- This is the bundled version of the additive relation proved above.
  apply AddCommGrpCat.hom_ext
  simpa using abelianSequenceColimitMap_comp_telescopeMap f

/-- Helper for Lemma 14.6.2: the coefficient of the telescope map at `0` is the original
coefficient at `0`. -/
lemma abelianSequenceTelescopeMap_coeff_zero (f : ∀ i : ℕ, A i →+ A (i + 1))
    (z : ⨁ i : ℕ, A i) :
    (abelianSequenceTelescopeMap f z) 0 = z 0 := by
  -- Reduce the coefficient computation to the direct-sum generators.
  refine DirectSum.induction_on z ?_ ?_ ?_
  · simp [abelianSequenceTelescopeMap]
  · intro i x
    by_cases h : i = 0
    · subst h
      have hzero : (DirectSum.of A 1 ((f 0) x)) 0 = 0 :=
        DirectSum.of_eq_of_ne (β := A) 1 0 ((f 0) x) (Nat.ne_of_lt (Nat.zero_lt_one))
      simp [abelianSequenceTelescopeMap, hzero]
    · simp [abelianSequenceTelescopeMap, DirectSum.of_eq_of_ne, h]
  · intro x y hx hy
    simp [hx, hy]

/-- Helper for Lemma 14.6.2: the coefficient of the telescope map at `n + 1` is
`z (n + 1) - f n (z n)`. -/
lemma abelianSequenceTelescopeMap_coeff_succ (f : ∀ i : ℕ, A i →+ A (i + 1))
    (z : ⨁ i : ℕ, A i) (n : ℕ) :
    (abelianSequenceTelescopeMap f z) (n + 1) = z (n + 1) - f n (z n) := by
  -- Reduce the coefficient computation to the direct-sum generators.
  refine DirectSum.induction_on z ?_ ?_ ?_
  · simp [abelianSequenceTelescopeMap]
  · intro i x
    by_cases hsucc : i = n + 1
    · subst hsucc
      have hpred : (DirectSum.of A (n + 1) x) n = 0 :=
        DirectSum.of_eq_of_ne (β := A) (n + 1) n x (Nat.ne_of_lt (Nat.lt_succ_self n))
      have hnext : (DirectSum.of A (n + 1 + 1) ((f (n + 1)) x)) (n + 1) = 0 :=
        DirectSum.of_eq_of_ne (β := A) (n + 1 + 1) (n + 1) ((f (n + 1)) x)
          (Nat.ne_of_lt (Nat.lt_succ_self (n + 1)))
      simp [abelianSequenceTelescopeMap, hpred, hnext]
    · by_cases hpred : i = n
      · subst hpred
        simp [abelianSequenceTelescopeMap]
      · have hsucc' : n + 1 ≠ i := fun h ↦ hsucc h.symm
        have hpred' : n ≠ i := fun h ↦ hpred h.symm
        simp [abelianSequenceTelescopeMap, DirectSum.of_eq_of_ne, hsucc', hpred']
  · intro x y hx hy
    simp [hx, hy, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- The canonical short complex attached to a sequential direct system of abelian groups. -/
noncomputable def abelianSequenceShortComplex (f : ∀ i : ℕ, A i →+ A (i + 1)) :
    ShortComplex Ab :=
  ShortComplex.mk
    (AddCommGrpCat.ofHom (abelianSequenceTelescopeMap f))
    (AddCommGrpCat.ofHom (abelianSequenceColimitMap f))
    (abelianSequenceColimitMap_comp_telescopeMap_hom f)

/-- Lemma 14.6.2. For a sequence of abelian groups `A i` with maps
`f i : A i →+ A (i + 1)`, the colimit fits into the short exact sequence
`0 ⟶ ⨁ i, A i ⟶ ⨁ i, A i ⟶ AddCommGroup.DirectLimit A (abelianSequenceMap f) ⟶ 0`
defined by the telescope map and the canonical colimit map. -/
theorem abelianSequenceDirectLimitShortExact (f : ∀ i : ℕ, A i →+ A (i + 1)) :
    (abelianSequenceShortComplex f).ShortExact :=
by
  have hCokernel :
      Limits.IsColimit
        (Limits.CokernelCofork.ofπ
          (AddCommGrpCat.ofHom (abelianSequenceColimitMap f))
          (abelianSequenceColimitMap_comp_telescopeMap_hom f)) := by
    -- Descend any map annihilating the telescope relation through
    -- the direct-limit universal property.
    refine Limits.CokernelCofork.IsColimit.ofπ _ _ ?_ ?_ ?_
    · intro Z g hg
      have hstep :
          ∀ i (x : A i), g (DirectSum.of A (i + 1) (f i x)) = g (DirectSum.of A i x) := by
        intro i x
        have hrelation := ConcreteCategory.congr_hom hg (DirectSum.of A i x)
        have hsub : g (DirectSum.of A i x) - g (DirectSum.of A (i + 1) (f i x)) = 0 := by
          simpa [abelianSequenceTelescopeMap, AddMonoidHom.comp_apply] using hrelation
        exact (sub_eq_zero.mp hsub).symm
      have hcompat :
          ∀ i j (hij : i ≤ j) (x : A i),
            g (DirectSum.of A j (abelianSequenceMap f i j hij x)) = g (DirectSum.of A i x) := by
        intro i j hij x
        induction j, hij using Nat.le_induction with
        | base =>
            rw [DirectedSystem.map_self (f := (abelianSequenceMap f · · ·)) x]
        | succ j hij ih =>
            rw [abelianSequenceMap_step f hij x]
            exact (hstep j _).trans ih
      exact AddCommGrpCat.ofHom <|
        AddCommGroup.DirectLimit.lift A (abelianSequenceMap f) Z
          (fun i ↦ g.hom.comp (DirectSum.of A i)) hcompat
    · intro Z g hg
      -- The descended morphism agrees with the original map on every direct-sum generator.
      have hstep :
          ∀ i (x : A i), g (DirectSum.of A (i + 1) (f i x)) = g (DirectSum.of A i x) := by
        intro i x
        have hrelation := ConcreteCategory.congr_hom hg (DirectSum.of A i x)
        have hsub : g (DirectSum.of A i x) - g (DirectSum.of A (i + 1) (f i x)) = 0 := by
          simpa [abelianSequenceTelescopeMap, AddMonoidHom.comp_apply] using hrelation
        exact (sub_eq_zero.mp hsub).symm
      have hcompat :
          ∀ i j (hij : i ≤ j) (x : A i),
            g (DirectSum.of A j (abelianSequenceMap f i j hij x)) = g (DirectSum.of A i x) := by
        intro i j hij x
        induction j, hij using Nat.le_induction with
        | base =>
            rw [DirectedSystem.map_self (f := (abelianSequenceMap f · · ·)) x]
        | succ j hij ih =>
            rw [abelianSequenceMap_step f hij x]
            exact (hstep j _).trans ih
      apply AddCommGrpCat.hom_ext
      apply DirectSum.addHom_ext
      intro i x
      simp [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom, AddMonoidHom.comp_apply,
        abelianSequenceColimitMap, DirectSum.toAddMonoid_of, AddCommGroup.DirectLimit.lift_of]
    · intro Z g hg m hm
      -- Uniqueness follows by comparing after precomposing with each canonical map into the limit.
      have hstep :
          ∀ i (x : A i), g (DirectSum.of A (i + 1) (f i x)) = g (DirectSum.of A i x) := by
        intro i x
        have hrelation := ConcreteCategory.congr_hom hg (DirectSum.of A i x)
        have hsub : g (DirectSum.of A i x) - g (DirectSum.of A (i + 1) (f i x)) = 0 := by
          simpa [abelianSequenceTelescopeMap, AddMonoidHom.comp_apply] using hrelation
        exact (sub_eq_zero.mp hsub).symm
      have hcompat :
          ∀ i j (hij : i ≤ j) (x : A i),
            g (DirectSum.of A j (abelianSequenceMap f i j hij x)) = g (DirectSum.of A i x) := by
        intro i j hij x
        induction j, hij using Nat.le_induction with
        | base =>
            rw [DirectedSystem.map_self (f := (abelianSequenceMap f · · ·)) x]
        | succ j hij ih =>
            rw [abelianSequenceMap_step f hij x]
            exact (hstep j _).trans ih
      apply AddCommGrpCat.hom_ext
      apply AddCommGroup.DirectLimit.hom_ext (P := Z)
      intro i
      apply AddMonoidHom.ext
      intro x
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
      change
        (AddCommGrpCat.Hom.hom m) ((AddCommGroup.DirectLimit.of A (abelianSequenceMap f) i) x) =
        (AddCommGroup.DirectLimit.lift A (abelianSequenceMap f) (↑Z)
          (fun i ↦ (AddCommGrpCat.Hom.hom g).comp (DirectSum.of A i)) hcompat)
          ((AddCommGroup.DirectLimit.of A (abelianSequenceMap f) i) x)
      rw [AddCommGroup.DirectLimit.lift_of]
      have hgenerator := ConcreteCategory.congr_hom hm (DirectSum.of A i x)
      simpa [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom, AddMonoidHom.comp_apply,
        abelianSequenceColimitMap, DirectSum.toAddMonoid_of] using hgenerator
  have hExact : (abelianSequenceShortComplex f).Exact := by
    -- Exactness is the standard consequence of a cokernel description of the right map.
    simpa [abelianSequenceShortComplex] using
      ShortComplex.exact_of_g_is_cokernel (abelianSequenceShortComplex f) hCokernel
  have hMono : Mono (AddCommGrpCat.ofHom (abelianSequenceTelescopeMap f)) := by
    -- The telescope map is injective because its coefficients satisfy a finite-support recursion.
    rw [AddCommGrpCat.mono_iff_injective]
    have hKernelZero : ∀ z : ⨁ i : ℕ, A i, abelianSequenceTelescopeMap f z = 0 → z = 0 := by
      intro z hz
      ext n
      induction n with
      | zero =>
          have hzero := congrArg (fun w : ⨁ i : ℕ, A i => w 0) hz
          simpa [abelianSequenceTelescopeMap_coeff_zero] using hzero
      | succ n ih =>
          have hsucc := congrArg (fun w : ⨁ i : ℕ, A i => w (n + 1)) hz
          have hcoeff : z (n + 1) - f n (z n) = 0 := by
            simpa [abelianSequenceTelescopeMap_coeff_succ] using hsucc
          simpa [ih] using hcoeff
    intro z w hzw
    have hEq : abelianSequenceTelescopeMap f z = abelianSequenceTelescopeMap f w := by
      simpa using hzw
    have hsub : abelianSequenceTelescopeMap f (z - w) = 0 := by
      rw [AddMonoidHom.map_sub, hEq, sub_self]
    exact sub_eq_zero.mp (hKernelZero (z - w) hsub)
  have hEpi : Epi (AddCommGrpCat.ofHom (abelianSequenceColimitMap f)) := by
    -- A cokernel map is automatically an epimorphism.
    simpa using Limits.epi_of_isColimit_cofork hCokernel
  -- Assemble exactness, injectivity, and surjectivity into a short exact sequence.
  exact ShortComplex.ShortExact.mk' hExact hMono hEpi

/-- The telescope sequence for `A₀ ⟶ A₁ ⟶ A₂ ⟶ ⋯` is exact in the function-level sense. -/
theorem abelianSequenceDirectLimit_exact (f : ∀ i : ℕ, A i →+ A (i + 1)) :
    Function.Exact (abelianSequenceTelescopeMap f) (abelianSequenceColimitMap f) := by
  simpa [abelianSequenceShortComplex] using
    (ShortComplex.ab_exact_iff_function_exact (abelianSequenceShortComplex f)).1
      (abelianSequenceDirectLimitShortExact f).exact

/-- The telescope map for a sequential direct limit of abelian groups is injective. -/
theorem abelianSequenceTelescopeMap_injective (f : ∀ i : ℕ, A i →+ A (i + 1)) :
    Function.Injective (abelianSequenceTelescopeMap f) := by
  simpa [abelianSequenceShortComplex] using
    ShortComplex.ShortExact.ab_injective_f (abelianSequenceDirectLimitShortExact f)

/-- The canonical map from the direct sum to the sequential direct limit is surjective. -/
theorem abelianSequenceColimitMap_surjective (f : ∀ i : ℕ, A i →+ A (i + 1)) :
    Function.Surjective (abelianSequenceColimitMap f) := by
  simpa [abelianSequenceShortComplex] using
    ShortComplex.ShortExact.ab_surjective_g (abelianSequenceDirectLimitShortExact f)
