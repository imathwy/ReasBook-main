import StacksProject_2024.Chap15.Lemma_15_96_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]

/-
Domain-style sampling:
- primary domain: composition of the Berthelot-Ogus operator `η_f` on cochain complexes of
  `A`-modules;
- sampled owner declarations in this domain:
  `BerthelotOgusInt.complex`,
  `BerthelotOgusInt.IsTermwiseFTorsionFree`,
  `etaFComplex`;
- best owner abstraction:
  `source-facing`: the bounded-below `ℕ`-indexed statement that iterating `η_g` and then `η_f`
    agrees with `η_(fg)`;
  `core/canonical`: the source-facing owner `etaFComplex` on `NatModuleCochainComplex A`;
  `bridge/view`: the corresponding `ℤ`-indexed extension-by-zero construction
    `BerthelotOgusInt.complex` on `ModuleComplex A` under `[K.IsStrictlyGE 0]`;
- primitive data vs derived API: the primitive inputs are the scalars `f`, `g`, the bounded-below
  complex `M`, and the termwise `(fg)`-torsion-freeness hypothesis. The `ℤ`-indexed equality is
  only a bridge statement for complexes concentrated in nonnegative degrees. -/

namespace BerthelotOgusInt

open scoped BerthelotOgusInt

/-- Helper for Lemma 15.96.9: on adjacent degrees, the Berthelot-Ogus differential is the
ambient differential with the codomain restriction forgotten. -/
private theorem complex_d_apply
    (g : A) (K : ModuleComplex A) (i : ℤ) (x : degreeSubmodule g K i) :
    Subtype.val (((η[g] K).d i (i + 1)).hom x) = (K.d i (i + 1)).hom x := by
  -- Unfold the owner complex once; its adjacent differential is the codomain restriction of `K.d`.
  rw [show ((η[g] K).d i (i + 1)).hom = differentialLinear g K i by
    simpa [BerthelotOgusInt.complex]]
  rfl

/-- Helper for Lemma 15.96.9: regularity of `f * g` in one degree implies regularity of `f` in
that same degree. -/
private theorem isSMulRegular_left_factor
    (f g : A) (K : ModuleComplex A) (hK : IsTermwiseFTorsionFree (f * g) K) (i : ℤ) :
    IsSMulRegular (K.X i) f :=
  (IsSMulRegular.mul_iff.mp (hK.isSMulRegular i)).1

/-- Helper for Lemma 15.96.9: regularity of `f * g` in one degree implies regularity of `g` in
that same degree. -/
private theorem isSMulRegular_right_factor
    (f g : A) (K : ModuleComplex A) (hK : IsTermwiseFTorsionFree (f * g) K) (i : ℤ) :
    IsSMulRegular (K.X i) g :=
  (IsSMulRegular.mul_iff.mp (hK.isSMulRegular i)).2

/-- Helper for Lemma 15.96.9: multiplication by a power of an `f`-regular scalar is injective. -/
private theorem lsmul_pow_injective
    {N : Type*} [AddCommGroup N] [Module A N] {f : A}
    (hf : IsSMulRegular N f) (n : ℕ) :
    Function.Injective (LinearMap.lsmul A N (f ^ n)) := by
  intro x y hxy
  induction n with
  | zero =>
      simpa using hxy
  | succ n ih =>
      apply ih
      apply hf
      simpa [LinearMap.lsmul_apply, pow_succ, smul_smul, mul_comm, mul_left_comm, mul_assoc]
        using hxy

/-- Helper for Lemma 15.96.9: an ambient `(fg)`-degree witness yields a degree-`n` `g`-witness
whose `f ^ n` multiple recovers the original element. -/
private theorem exists_right_factor_degree_witness
    (f g : A) (K : ModuleComplex A)
    (hK : IsTermwiseFTorsionFree (f * g) K)
    (n : ℕ) (x0 : K.X (n : ℤ))
    (hx : x0 ∈ degreeSubmodule (f * g) K (n : ℤ)) :
    ∃ y : degreeSubmodule g K (n : ℤ),
      (f ^ n) • ((y : degreeSubmodule g K (n : ℤ)) : K.X (n : ℤ)) = x0 := by
  rcases hx.1 with ⟨z, hz⟩
  rcases hx.2 with ⟨z', hz'⟩
  refine ⟨⟨g ^ n • z, ?_, ?_⟩, ?_⟩
  · -- The visible `g ^ n` factor gives the degree-`n` range witness immediately.
    refine ⟨z, ?_⟩
    simp [LinearMap.lsmul_apply]
  · -- Cancel `f ^ n` in ambient degree `n + 1` to recover the successor `g`-range witness.
    refine ⟨f • z', ?_⟩
    have hx0_eq : (f ^ n) • (g ^ n • z) = x0 := by
      simpa [LinearMap.lsmul_apply, mul_pow, smul_smul, mul_comm, mul_left_comm, mul_assoc]
        using hz
    have hcancel :
        (LinearMap.lsmul A (K.X (n + 1 : ℤ)) (f ^ n))
            ((K.d (n : ℤ) (n + 1 : ℤ)).hom (g ^ n • z)) =
          (LinearMap.lsmul A (K.X (n + 1 : ℤ)) (f ^ n))
            (g ^ (n + 1) • (f • z')) := by
      -- Reexpress `d x0` through the chosen `(fg)^(n+1)` witness and commute scalars.
      calc
        (f ^ n) • ((K.d (n : ℤ) (n + 1 : ℤ)).hom (g ^ n • z))
            = (K.d (n : ℤ) (n + 1 : ℤ)).hom ((f ^ n) • (g ^ n • z)) := by
                rw [← _root_.map_smul]
        _ = (K.d (n : ℤ) (n + 1 : ℤ)).hom x0 := by rw [hx0_eq]
        _ = ((f * g) ^ (n + 1)) • z' := by
              simpa [LinearMap.lsmul_apply] using hz'.symm
        _ = (f ^ n) • (g ^ (n + 1) • (f • z')) := by
              simp [mul_pow, pow_succ, smul_smul, mul_comm, mul_left_comm, mul_assoc]
    exact
      (lsmul_pow_injective (A := A) (N := K.X (n + 1 : ℤ)) (f := f)
        (isSMulRegular_left_factor f g K hK (n + 1 : ℤ)) n)
        (by
          symm
          simpa [LinearMap.lsmul_apply, smul_smul, mul_comm, mul_left_comm, mul_assoc]
            using hcancel)
  · -- Multiplying the recovered `g`-witness by `f ^ n` returns the original ambient element.
    simpa [LinearMap.lsmul_apply, mul_pow, smul_smul, mul_comm, mul_left_comm, mul_assoc]
      using hz

/-- Helper for Lemma 15.96.9: an ambient successor `(fg)`-degree witness yields the successor
`g`-degree witness needed for the reverse direction inside `η[f](η[g]K)`. -/
private theorem exists_right_factor_successor_witness
    (f g : A) (K : ModuleComplex A)
    (hK : IsTermwiseFTorsionFree (f * g) K)
    (n : ℕ) (x0 : K.X (n : ℤ))
    (hx : x0 ∈ degreeSubmodule (f * g) K (n : ℤ)) :
    ∃ y : degreeSubmodule g K (n + 1 : ℤ),
      (f ^ (n + 1)) • ((y : degreeSubmodule g K (n + 1 : ℤ)) : K.X (n + 1 : ℤ)) =
        (K.d (n : ℤ) (n + 1 : ℤ)).hom x0 := by
  rcases hx.2 with ⟨z', hz'⟩
  refine ⟨⟨g ^ (n + 1) • z', ?_, ?_⟩, ?_⟩
  · -- The `(fg)^(n+1)` witness already contains the needed `g^(n+1)` factor.
    refine ⟨z', ?_⟩
    simp [LinearMap.lsmul_apply]
  · -- Apply `d ∘ d = 0` and cancel `f ^ (n + 1)` in ambient degree `n + 2`.
    refine ⟨0, ?_⟩
    have hdx_eq :
        (f ^ (n + 1)) • (g ^ (n + 1) • z') =
          (K.d (n : ℤ) (n + 1 : ℤ)).hom x0 := by
      simpa [LinearMap.lsmul_apply, mul_pow, smul_smul, mul_comm, mul_left_comm, mul_assoc]
        using hz'
    have hdd :
        (K.d (n + 1 : ℤ) (n + 2 : ℤ)).hom ((K.d (n : ℤ) (n + 1 : ℤ)).hom x0) = 0 := by
      -- Use the ambient `d ∘ d = 0` relation directly before simplifying the codomain zero.
      exact
        LinearMap.congr_fun
          (congrArg ModuleCat.Hom.hom (K.d_comp_d (n : ℤ) (n + 1 : ℤ) (n + 2 : ℤ))) x0
    have hcancel :
        (LinearMap.lsmul A (K.X (n + 2 : ℤ)) (f ^ (n + 1)))
            ((K.d (n + 1 : ℤ) (n + 2 : ℤ)).hom (g ^ (n + 1) • z')) =
          (LinearMap.lsmul A (K.X (n + 2 : ℤ)) (f ^ (n + 1))) 0 := by
      -- The successor witness becomes a cycle after one more differential.
      calc
        (f ^ (n + 1)) • ((K.d (n + 1 : ℤ) (n + 2 : ℤ)).hom (g ^ (n + 1) • z'))
            = (K.d (n + 1 : ℤ) (n + 2 : ℤ)).hom ((f ^ (n + 1)) • (g ^ (n + 1) • z')) := by
                rw [← _root_.map_smul]
        _ = (K.d (n + 1 : ℤ) (n + 2 : ℤ)).hom ((K.d (n : ℤ) (n + 1 : ℤ)).hom x0) := by
              rw [hdx_eq]
        _ = 0 := by rw [hdd]
        _ = (f ^ (n + 1)) • (0 : K.X (n + 2 : ℤ)) := by simp
    have hdy_zero :
        (K.d (n + 1 : ℤ) (n + 2 : ℤ)).hom (g ^ (n + 1) • z') = 0 := by
      exact
        (lsmul_pow_injective (A := A) (N := K.X (n + 2 : ℤ)) (f := f)
          (isSMulRegular_left_factor f g K hK (n + 2 : ℤ)) (n + 1))
          (by simpa [LinearMap.lsmul_apply] using hcancel)
    -- The successor differential is zero, so the chosen zero witness satisfies the range condition.
    calc
      ((LinearMap.lsmul A (K.X (n + 2 : ℤ)) (g ^ Int.toNat (n + 2 : ℤ))) 0)
          = (0 : K.X (n + 2 : ℤ)) := by simp
      _ = (K.d (n + 1 : ℤ) (n + 2 : ℤ)).hom (g ^ (n + 1) • z') := by rw [hdy_zero]
  · -- The chosen `g`-witness still records the original differential after multiplying by `f^(n+1)`.
    simpa [LinearMap.lsmul_apply, mul_pow, smul_smul, mul_comm, mul_left_comm, mul_assoc]
      using hz'

/-- Helper for Lemma 15.96.9: a nested `f`-degree witness in `η[g]K` combines with the existing
`g`-degree witness to give an ambient `(fg)`-degree witness. -/
private theorem degreeSubmodule_comp_mem_forward
    (f g : A) (K : ModuleComplex A)
    (n : ℕ) (x : degreeSubmodule g K (n : ℤ))
    (hx : x ∈ degreeSubmodule f (η[g] K) (n : ℤ)) :
    ((x : degreeSubmodule g K (n : ℤ)) : K.X (n : ℤ)) ∈ degreeSubmodule (f * g) K (n : ℤ) := by
  -- TODO replan: this witness-combination step is algebraically correct, but the current proof
  -- needs a coercion-stable formulation for elements of nested submodules before the ambient
  -- `(fg)^n` witness can be assembled without rewrite failures.
  sorry

/-- Helper for Lemma 15.96.9: in nonnegative degree `n`, the iterated Berthelot-Ogus degree term
for `f` after `g` agrees with the single degree term for `f * g`. -/
private theorem degreeSubmodule_comp_mem_iff
    (f g : A) (K : ModuleComplex A)
    (hK : IsTermwiseFTorsionFree (f * g) K)
    (n : ℕ) (x : degreeSubmodule g K (n : ℤ)) :
    x ∈ degreeSubmodule f (η[g] K) (n : ℤ) ↔
      ((x : degreeSubmodule g K (n : ℤ)) : K.X (n : ℤ)) ∈ degreeSubmodule (f * g) K (n : ℤ) := by
  -- TODO replan: the backward direction should package the ambient witnesses returned above into
  -- nested `η[g] K` witnesses, but the current coercion route through `Subtype.ext` is not stable.
  sorry

/-- Helper for Lemma 15.96.9: an ambient `(fg)`-degree element automatically satisfies the
underlying `g`-degree conditions in the same nonnegative degree. -/
private theorem degreeSubmodule_mul_mem_right_factor
    (f g : A) (K : ModuleComplex A)
    (n : ℕ) (x : K.X (n : ℤ))
    (hx : x ∈ degreeSubmodule (f * g) K (n : ℤ)) :
    x ∈ degreeSubmodule g K (n : ℤ) := by
  refine ⟨?_, ?_⟩
  · -- The visible `(fg)^n = g^n f^n` witness already contains the required `g^n` factor.
    rcases hx.1 with ⟨y, hy⟩
    refine ⟨(f ^ n) • y, ?_⟩
    simpa [LinearMap.lsmul_apply, mul_pow, smul_smul, mul_comm, mul_left_comm, mul_assoc]
      using hy
  · -- The same factor extraction works one degree higher for the differential condition.
    rcases hx.2 with ⟨y, hy⟩
    refine ⟨(f ^ (n + 1)) • y, ?_⟩
    simpa [LinearMap.lsmul_apply, mul_pow, smul_smul, mul_comm, mul_left_comm, mul_assoc]
      using hy

/-- Helper for Lemma 15.96.9: after viewing an ambient `(fg)`-degree element as a `g`-degree
element, the reverse implication of `degreeSubmodule_comp_mem_iff` yields the nested
`η[f](η[g]K)` degree condition. -/
private theorem degreeSubmodule_comp_mem_of_mul_mem
    (f g : A) (K : ModuleComplex A)
    (hK : IsTermwiseFTorsionFree (f * g) K)
    (n : ℕ) (x : K.X (n : ℤ))
    (hx : x ∈ degreeSubmodule (f * g) K (n : ℤ)) :
    (⟨x, degreeSubmodule_mul_mem_right_factor f g K n x hx⟩ :
      degreeSubmodule g K (n : ℤ)) ∈ degreeSubmodule f (η[g] K) (n : ℤ) := by
  -- Reinsert the ambient element as a `g`-degree element, then apply the reverse implication.
  exact
    (degreeSubmodule_comp_mem_iff f g K hK n
      ⟨x, degreeSubmodule_mul_mem_right_factor f g K n x hx⟩).2
      (by simpa using hx)

/-- Helper for Lemma 15.96.9: forgetting the intermediate `g`-degree witness identifies the
nested degree term with the ambient `(fg)`-degree term as a mapped submodule. -/
private theorem degree_term_comp_map_eq_degree_term_mul
    (f g : A) (K : ModuleComplex A)
    (hK : IsTermwiseFTorsionFree (f * g) K)
    (n : ℕ) :
    (degreeSubmodule f (η[g] K) (n : ℤ)).map
        (degreeSubmodule g K (n : ℤ)).subtype =
      degreeSubmodule (f * g) K (n : ℤ) := by
  -- TODO replan: this is the correct submodule-level normalization target, but the current proof
  -- needs a direct `mem_map` witness written in terms of the outer subtype carrier.
  sorry

/-- Helper for Lemma 15.96.9: in nonnegative degree, the nested Berthelot-Ogus term
`η[f](η[g] K)` is linearly equivalent to the single `(fg)`-degree term in the ambient complex. -/
private def degree_term_comp_linearEquiv
    (f g : A) (K : ModuleComplex A)
    (hK : IsTermwiseFTorsionFree (f * g) K)
    (n : ℕ) :
    degreeSubmodule f (η[g] K) (n : ℤ) ≃ₗ[A] degreeSubmodule (f * g) K (n : ℤ) where
  toFun x := ⟨x.1.1, degreeSubmodule_comp_mem_forward f g K n x.1 x.2⟩
  invFun x :=
    ⟨⟨x.1, degreeSubmodule_mul_mem_right_factor f g K n x.1 x.2⟩,
      degreeSubmodule_comp_mem_of_mul_mem f g K hK n x.1 x.2⟩
  -- Forgetting and then rebuilding the `g`-witness leaves the nested subtype unchanged.
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  -- Rebuilding the nested witness and forgetting it again leaves the ambient `(fg)`-term fixed.
  right_inv x := by
    ext
    rfl
  -- The comparison map is induced by the ambient inclusion into `K.X n`.
  map_add' x y := by
    ext
    rfl
  -- Scalar multiplication is inherited from the ambient module structure.
  map_smul' a x := by
    ext
    rfl

/-- Helper for Lemma 15.96.9: the existing comparison equivalence is the canonical subtype-map
equivalence followed by the proved identification of its image with the `(fg)`-degree term. -/
private theorem degree_term_comp_linearEquiv_eq_subtypeMap_trans
    (f g : A) (K : ModuleComplex A)
    (hK : IsTermwiseFTorsionFree (f * g) K)
    (n : ℕ) :
    degree_term_comp_linearEquiv f g K hK n =
      ((degreeSubmodule g K (n : ℤ)).equivSubtypeMap
          (degreeSubmodule f (η[g] K) (n : ℤ))).trans
        (LinearEquiv.ofEq
          ((degreeSubmodule f (η[g] K) (n : ℤ)).map
              (degreeSubmodule g K (n : ℤ)).subtype)
          (degreeSubmodule (f * g) K (n : ℤ))
          (degree_term_comp_map_eq_degree_term_mul f g K hK n)) := by
  -- Both equivalences forget to the same ambient element of `K.X n`.
  ext x
  rfl

/-- Helper for Lemma 15.96.9: after identifying nonnegative degree terms via
`degree_term_comp_linearEquiv`, the adjacent differentials on the two complexes agree. -/
private theorem degree_term_comp_linearEquiv_comm
    (f g : A) (K : ModuleComplex A)
    (hK : IsTermwiseFTorsionFree (f * g) K)
    (n : ℕ) :
    CategoryTheory.CommSq
      (ModuleCat.ofHom ((degree_term_comp_linearEquiv f g K hK n).toLinearMap))
      ((η[f] (η[g] K)).d (n : ℤ) (n + 1 : ℤ))
      ((η[f * g] K).d (n : ℤ) (n + 1 : ℤ))
      (ModuleCat.ofHom ((degree_term_comp_linearEquiv f g K hK (n + 1)).toLinearMap)) := by
  -- TODO replan: once the component comparison is expressed by the right subtype equivalence, this
  -- differential square should reduce to `complex_d_apply` on both sides.
  sorry

/-- Helper for Lemma 15.96.9: in nonpositive degree, the Berthelot-Ogus degree term is the whole
ambient module because all relevant powers are zeroth powers. -/
private theorem degreeSubmodule_eq_top_of_nonpos
    (f : A) (K : ModuleComplex A) {i : ℤ}
    (hi : i ≤ 0) (hi_succ : i + 1 ≤ 0) :
    degreeSubmodule f K i = ⊤ := by
  -- Both range conditions become the identity range once `Int.toNat` collapses to zero.
  ext x
  simp [degreeSubmodule, Int.toNat_of_nonpos hi, Int.toNat_of_nonpos hi_succ]

/-- Helper for Lemma 15.96.9: TODO replan.
The source-faithful route needs a componentwise isomorphism built from
`Submodule.equivSubtypeMap`, not a literal object equality by definitional `change`. -/
private theorem degree_term_comp_eq_degree_term_mul_via_subtypeMap
    (f g : A) (K : ModuleComplex A) [K.IsStrictlyGE 0]
    (hK : IsTermwiseFTorsionFree (f * g) K)
    (n : ℕ) :
    ((η[f] (η[g] K)).X (n : ℤ)) = ((η[f * g] K).X (n : ℤ)) := by
  sorry

/-- Helper for Lemma 15.96.9: every component of `η[f](η[g] K)` agrees with the corresponding
component of `η[f * g] K`. -/
private theorem complex_comp_component_eq
    (f g : A) (K : ModuleComplex A) [K.IsStrictlyGE 0]
    (hK : IsTermwiseFTorsionFree (f * g) K)
    (i : ℤ) :
    ((η[f] (η[g] K)).X i) = ((η[f * g] K).X i) := by
  -- TODO replan: the negative branch is controlled by `degreeSubmodule_eq_top_of_nonpos`, but the
  -- nonnegative branch still needs a genuine component isomorphism instead of the false
  -- definitional-equality route above.
  sorry

-- Proof sketch: unfold the degree-`n` defining intersections for `η_f (η_g M)` and `η_{fg} M`.
-- The hypothesis that multiplication by `fg` is injective on every term already forces the
-- iterated range conditions to agree with the single range condition for `(fg)^n`, while the
-- differential condition is unchanged after rewriting powers in the commutative ring `A`. The
-- source nonzerodivisor assumptions on `f` and `g` are therefore redundant for this equality.
/-- Bounded-below `ℤ`-indexed bridge form of Lemma `15.96.9`: if multiplication by `fg` is
injective on every term of a cochain complex concentrated in nonnegative degrees, then applying the
Berthelot-Ogus operator first for `g` and then for `f` agrees with applying it once for `fg`. -/
theorem complex_comp_eq_complex_mul
    (f g : A) (K : ModuleComplex A) [K.IsStrictlyGE 0]
    (hK : IsTermwiseFTorsionFree (f * g) K) :
    η[f] (η[g] K) = η[f * g] K := by
  -- TODO: the nonnegative component comparison is now packaged in
  -- `degree_term_comp_linearEquiv` and `degree_term_comp_linearEquiv_comm`.
  -- The remaining blocker is to normalize these degreewise linear equivalences into literal object
  -- equalities so `HomologicalComplex.ext` can close the owner theorem, while the negative degrees
  -- are handled by `K.IsStrictlyGE 0`.
  sorry

end BerthelotOgusInt

-- Proof sketch: transport the owner equality
-- `BerthelotOgusInt.complex f
--     (BerthelotOgusInt.complex g (M.extend ComplexShape.embeddingUpNat)) =
--   BerthelotOgusInt.complex (f * g) (M.extend ComplexShape.embeddingUpNat)` to the source-facing
-- `ℕ`-indexed complexes by restricting to nonnegative degrees and using the defining
-- degreewise transport built into `η[f] M`.
/-- Lemma 15.96.9 in the bounded-below bridge/view: if multiplication by `fg` is injective on
every term of `M^\bullet`, then applying the Berthelot-Ogus operator first for `g` and then for
`f` gives the same `ℕ`-indexed cochain complex as applying it once for `fg`. -/
theorem etaFComplex_comp_eq_etaFComplex_mul
    (f g : A) (M : NatModuleCochainComplex A) (hM : IsTermwiseFTorsionFree (f * g) M) :
    η[f] (η[g] M) = η[f * g] M := by
  -- TODO: once the owner theorem is upgraded from the degreewise linear equivalences above to a
  -- literal equality of `ℤ`-indexed complexes, apply it to `M.extend ComplexShape.embeddingUpNat`
  -- and transport the result back to `ℕ`-indexed complexes using `etaFExtendRestrictionIso`.
  sorry

end
