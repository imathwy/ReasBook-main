import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Module (End toModuleEnd)
open scoped BigOperators

variable {A : Type u} [Ring A] [IsSimpleRing A]

/-- Helper for Lemma 11.3.1: left multiplication by an element of a right ideal stays in the
right ideal. -/
lemma rightIdeal_left_mul_mem {M : Submodule Aᵐᵒᵖ A} (m x : M) : ((m : A) * x : A) ∈ M := by
  -- A right ideal is closed under multiplication on the right by arbitrary ring elements.
  simpa using M.smul_mem (MulOpposite.op (x : A)) m.property

/-- Helper for Lemma 11.3.1: right multiplication by a ring element stays in the right ideal. -/
lemma rightIdeal_mul_right_mem {M : Submodule Aᵐᵒᵖ A} (x : M) (a : A) : ((x : A) * a : A) ∈ M := by
  -- This is exactly the defining closure of a right ideal.
  simpa using M.smul_mem (MulOpposite.op a) x.property

/-- Helper for Lemma 11.3.1: right multiplication preserves the left ideal spanned by a right
ideal. -/
lemma rightIdeal_span_mul_mem {M : Submodule Aᵐᵒᵖ A} {x : A} (hx : x ∈ Ideal.span (M : Set A))
    (a : A) : x * a ∈ Ideal.span (M : Set A) := by
  -- Proof comment: extend right-multiplication closure from the generators `M` to the whole
  -- left span `Ideal.span (M : Set A)` by span induction.
  refine Submodule.span_induction (p := fun y _ ↦ y * a ∈ Ideal.span (M : Set A)) ?_ ?_ ?_ ?_ hx
  · intro y hy
    exact Ideal.subset_span (rightIdeal_mul_right_mem ⟨y, hy⟩ a)
  · simpa using (Ideal.zero_mem (Ideal.span (M : Set A)))
  · intro y z _ _ hy hz
    simpa [add_mul] using Ideal.add_mem (Ideal.span (M : Set A)) hy hz
  · intro b y _ hy
    simpa [smul_eq_mul, mul_assoc] using Ideal.mul_mem_left (Ideal.span (M : Set A)) b hy

/-- Helper for Lemma 11.3.1: the left ideal spanned by a right ideal is automatically two-sided. -/
lemma rightIdeal_span_isTwoSided (M : Submodule Aᵐᵒᵖ A) :
    (Ideal.span (M : Set A)).IsTwoSided := by
  -- Proof comment: the previous lemma supplies the missing right-multiplication closure field.
  refine Ideal.IsTwoSided.mk ?_
  intro x a hx
  exact rightIdeal_span_mul_mem hx a

/-- Helper for Lemma 11.3.1: left multiplication by an element of the right ideal defines an
`Aᵐᵒᵖ`-linear endomorphism. -/
lemma left_mul_endomorphism_map_add {M : Submodule Aᵐᵒᵖ A} (m : M) :
    ∀ x y : M,
      (⟨(m : A) * (x + y), rightIdeal_left_mul_mem m (x + y)⟩ : M) =
        ⟨(m : A) * x, rightIdeal_left_mul_mem m x⟩ +
          ⟨(m : A) * y, rightIdeal_left_mul_mem m y⟩ := by
  -- Left multiplication distributes over addition in the ambient ring.
  intro x y
  apply Subtype.ext
  simp [mul_add]

/-- Helper for Lemma 11.3.1: left multiplication commutes with the right `A`-action. -/
lemma left_mul_endomorphism_map_smul {M : Submodule Aᵐᵒᵖ A} (m : M) :
    ∀ (a : Aᵐᵒᵖ) (x : M),
      (⟨(m : A) * (a • x : M), rightIdeal_left_mul_mem m (a • x : M)⟩ : M) =
        a • ⟨(m : A) * x, rightIdeal_left_mul_mem m x⟩ := by
  -- Associativity identifies the two ways of combining left and right multiplication.
  intro a x
  cases a
  apply Subtype.ext
  simp [mul_assoc]

/-- Helper for Lemma 11.3.1: the textbook left-multiplication operator on `M`. -/
def left_mul_endomorphism {M : Submodule Aᵐᵒᵖ A} (m : M) : End Aᵐᵒᵖ M :=
  { toFun := fun x ↦ ⟨(m : A) * x, rightIdeal_left_mul_mem m x⟩
    map_add' := left_mul_endomorphism_map_add m
    map_smul' := left_mul_endomorphism_map_smul m }

/-- Helper for Lemma 11.3.1: an attached finset element of `s` yields the corresponding element of
the right ideal. -/
def finset_rightIdeal_member {M : Submodule Aᵐᵒᵖ A} {s : Finset A} (hs : ↑s ⊆ (M : Set A))
    (m : {x // x ∈ s}) : M :=
  ⟨m.1, hs m.2⟩

/-- Helper for Lemma 11.3.1: multiplying an element of the right ideal by a coefficient on the
right stays in the right ideal. -/
def scaled_rightIdeal_member {M : Submodule Aᵐᵒᵖ A} (x : M) (a : A) : M :=
  ⟨(x : A) * a, rightIdeal_mul_right_mem x a⟩

/-- Helper for Lemma 11.3.1: an element of the bicommutant commutes with left multiplication by
elements of the right ideal. -/
lemma bicommutant_map_left_mul {M : Submodule Aᵐᵒᵖ A} (f : End (End Aᵐᵒᵖ M) M) (m x : M) :
    f (left_mul_endomorphism m x) = left_mul_endomorphism m (f x) := by
  -- Elements of the bicommutant are `End Aᵐᵒᵖ M`-linear, so they commute with every such scalar.
  simpa [Module.End.smul_def] using f.map_smul (left_mul_endomorphism m) x

/-- Helper for Lemma 11.3.1: a nonzero right ideal spans the unit ideal on the left. -/
lemma rightIdeal_span_eq_top_of_nonzero (M : Submodule Aᵐᵒᵖ A) (hM : M ≠ ⊥) :
    Ideal.span (M : Set A) = ⊤ := by
  let J : Ideal A := Ideal.span (M : Set A)
  have hJ_ne : J ≠ ⊥ := by
    -- Proof comment: a nonzero element of `M` remains nonzero in the span `J`.
    obtain ⟨m, hmM, hm0⟩ := (Submodule.ne_bot_iff _).mp hM
    have hmJ : m ∈ J := Ideal.subset_span hmM
    intro hJ
    have hmBot : m ∈ (⊥ : Ideal A) := by
      simpa [J, hJ] using hmJ
    exact hm0 (by simpa using hmBot)
  letI : J.IsTwoSided := by
    simpa [J] using rightIdeal_span_isTwoSided M
  -- Proof comment: simplicity leaves only the bottom and top two-sided ideals.
  rcases IsSimpleRing.simple.eq_bot_or_eq_top J.toTwoSided with hJ | hJ
  · have hJ' : J = ⊥ := by
      simpa [J] using congrArg TwoSidedIdeal.asIdeal hJ
    exact (hJ_ne hJ').elim
  · simpa [J] using congrArg TwoSidedIdeal.asIdeal hJ

/-- Helper for Lemma 11.3.1: a nonzero right ideal generates the unit as a finite left-linear
combination of its elements. -/
lemma exists_unit_relation_of_nonzero_right_ideal (M : Submodule Aᵐᵒᵖ A) (hM : M ≠ ⊥) :
    ∃ s : Finset A, ↑s ⊆ (M : Set A) ∧
      ∃ c : A → A, Finset.sum s (fun m ↦ c m * m) = 1 := by
  have hspan : Ideal.span (M : Set A) = ⊤ := rightIdeal_span_eq_top_of_nonzero M hM
  -- Proof comment: first shrink the unit ideal witness to a finite subset of `M`.
  obtain ⟨s, hs, hsTop⟩ := (Ideal.span_eq_top_iff_finite (M : Set A)).mp hspan
  have hOne : (1 : A) ∈ Ideal.span (s : Set A) := by
    -- Proof comment: rewrite the top-ideal statement as membership of `1`.
    simpa [Ideal.eq_top_iff_one] using hsTop
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 hOne
  -- Proof comment: `Submodule.mem_span_finset` already returns the required finite sum relation.
  exact ⟨s, hs, c, by simpa [smul_eq_mul] using hc⟩

/-- Helper for Lemma 11.3.1: a finite unit relation reconstructs any bicommutant endomorphism as
right multiplication by a single scalar. -/
lemma bicommutant_reconstruct_of_unit_relation {M : Submodule Aᵐᵒᵖ A}
    (f : End (End Aᵐᵒᵖ M) M) (s : Finset A) (hs : ↑s ⊆ (M : Set A)) (c : A → A)
    (hc : Finset.sum s (fun m ↦ c m * m) = 1) :
    let a := Finset.sum s.attach (fun m ↦ c m.1 * (f (finset_rightIdeal_member hs m) : A))
    ∀ x : M, (f x : A) = (x : A) * a := by
  intro a x
  have hx_decomp :
      x =
        Finset.sum s.attach
          (fun m ↦
            left_mul_endomorphism (scaled_rightIdeal_member x (c m.1))
              (finset_rightIdeal_member hs m)) := by
    -- Proof comment: rewrite `x = x * 1` using the chosen unit relation, then interpret each
    -- summand as left multiplication by an element of `M`.
    have hx_val :
        (x : A) = Finset.sum s.attach (fun m ↦ (((x : A) * c m.1) * m.1)) := by
      calc
        (x : A) = (x : A) * 1 := by simp
        _ = (x : A) * Finset.sum s (fun m ↦ c m * m) := by rw [hc]
        _ = Finset.sum s (fun m ↦ (x : A) * (c m * m)) := by rw [Finset.mul_sum]
        _ = Finset.sum s (fun m ↦ ((x : A) * c m) * m) := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              rw [mul_assoc]
        _ = Finset.sum s.attach (fun m ↦ (((x : A) * c m.1) * m.1)) := by
              simpa using (Finset.sum_attach s (fun m : A ↦ ((x : A) * c m) * m)).symm
    exact Subtype.ext (by
      simpa [left_mul_endomorphism, scaled_rightIdeal_member, finset_rightIdeal_member] using
        hx_val)
  -- Proof comment: applying `f` to the decomposition of `x` and expanding `f.map_sum` gives the
  -- desired finite sum expression on underlying ring elements.
  have hsum_apply :
      (f x : A) =
        Finset.sum s.attach
          (fun m ↦
            (f
              (left_mul_endomorphism (scaled_rightIdeal_member x (c m.1))
                (finset_rightIdeal_member hs m)) : A)) := by
    simpa [map_sum] using congrArg Subtype.val (congrArg f hx_decomp)
  -- Proof comment: apply `f` to the decomposition and commute `f` past each left-multiplication
  -- operator to isolate one common right-multiplication scalar.
  calc
    (f x : A)
        = Finset.sum s.attach
            (fun m ↦
              (f
                (left_mul_endomorphism (scaled_rightIdeal_member x (c m.1))
                  (finset_rightIdeal_member hs m)) : A)) := hsum_apply
    _ = Finset.sum s.attach
          (fun m ↦ (((x : A) * c m.1) * (f (finset_rightIdeal_member hs m) : A))) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            exact congrArg Subtype.val
              (bicommutant_map_left_mul f (scaled_rightIdeal_member x (c m.1))
                (finset_rightIdeal_member hs m))
    _ = Finset.sum s.attach
          (fun m ↦ (x : A) * (c m.1 * (f (finset_rightIdeal_member hs m) : A))) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            rw [mul_assoc]
    _ = (x : A) *
          Finset.sum s.attach
            (fun m ↦ c m.1 * (f (finset_rightIdeal_member hs m) : A)) := by
            rw [← Finset.mul_sum]
    _ = (x : A) * a := by
            rfl

/-- Helper for Lemma 11.3.1: the canonical map from the opposite ring to the bicommutant is
surjective for a nonzero right ideal. -/
lemma rightIdeal_bicommutant_surjective (M : Submodule Aᵐᵒᵖ A) (hM : M ≠ ⊥) :
    Function.Surjective (toModuleEnd (End Aᵐᵒᵖ M) M : Aᵐᵒᵖ →+* End (End Aᵐᵒᵖ M) M) := by
  intro f
  obtain ⟨s, hs, c, hc⟩ := exists_unit_relation_of_nonzero_right_ideal M hM
  let a : A := Finset.sum s.attach
    (fun m ↦ c m.1 * (f (finset_rightIdeal_member hs m) : A))
  refine ⟨MulOpposite.op a, ?_⟩
  ext x
  -- Proof comment: the reconstruction lemma identifies `f` with the endomorphism
  -- `x ↦ x * a`, which is definitionally `toModuleEnd (MulOpposite.op a)`.
  simpa only [a] using
    (bicommutant_reconstruct_of_unit_relation (M := M) (f := f) (s := s) (hs := hs) (c := c)
      (hc := hc) x).symm

/-- Lemma 11.3.1: if `A` is a simple ring and `M` is a nonzero right ideal of `A`, then the
canonical right-multiplication map from `Aᵐᵒᵖ` to the bicommutant
`End (End Aᵐᵒᵖ M) M` is bijective. In owner-abstraction form this is the canonical
map `toModuleEnd`, while the textbook `Algebra.lsmul ℤ (End Aᵐᵒᵖ M) M` is the
same action viewed as an algebra homomorphism. -/
-- Proof sketch: injectivity comes from simplicity of `A`, since a nonzero right ideal makes the
-- bicommutant nontrivial. For surjectivity, show that the image is a nonzero right ideal in the
-- bicommutant and then use the simplicity argument from the textbook to force it to be all of the
-- bicommutant.
theorem rightIdeal_bicommutant_bijective (M : Submodule Aᵐᵒᵖ A) (hM : M ≠ ⊥) :
    Function.Bijective (toModuleEnd (End Aᵐᵒᵖ M) M : Aᵐᵒᵖ →+* _) := by
  -- Split the textbook argument into injectivity from simplicity and surjectivity from
  -- the finite unit relation extracted above.
  have hNontrivialM : Nontrivial M := by
    obtain ⟨m, hmM, hm0⟩ := (Submodule.ne_bot_iff _).mp hM
    refine ⟨⟨0, M.zero_mem⟩, ⟨m, hmM⟩, ?_⟩
    intro hEq
    exact hm0 (congrArg Subtype.val hEq).symm
  let _ : Nontrivial M := hNontrivialM
  exact ⟨RingHom.injective _, rightIdeal_bicommutant_surjective M hM⟩

/-- Companion bridge: the textbook `ℤ`-algebra form of Lemma 11.3.1 is the same canonical map. -/
theorem rightIdeal_bicommutant_lsmul_bijective (M : Submodule Aᵐᵒᵖ A) (hM : M ≠ ⊥) :
    Function.Bijective (Algebra.lsmul ℤ (End Aᵐᵒᵖ M) M : Aᵐᵒᵖ →ₐ[ℤ] _) := by
  simpa using rightIdeal_bicommutant_bijective M hM

/-- Owner abstraction underlying Lemma 11.3.1: the bicommutant of a nonzero right ideal of a
simple ring recovers the original opposite ring. -/
noncomputable def rightIdeal_double_centralizer (M : Submodule Aᵐᵒᵖ A) (hM : M ≠ ⊥) :
    Aᵐᵒᵖ ≃+* End (End Aᵐᵒᵖ M) M :=
  RingEquiv.ofBijective (toModuleEnd (End Aᵐᵒᵖ M) M : Aᵐᵒᵖ →+* _)
    (rightIdeal_bicommutant_bijective M hM)

end
