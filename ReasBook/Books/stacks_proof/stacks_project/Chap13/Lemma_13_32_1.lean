import Mathlib
import stacks_proof.stacks_project.Chap13.Lemma_13_15_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open HomologicalComplex
open scoped ZeroObject

universe v u

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma 13.32.1:
- primary domain: cohomological-dimension functions controlling object-property replacements of
  cochain complexes in an abelian category;
- sampled owner declarations:
  `ObjectProperty.ContainsZero`,
  `ObjectProperty.HasMonoEmbedding`,
  `exists_quasiIso_with_terms_in_of_isZero_homology_below`;
- best owner abstraction: the categorical owner is the zero-locus object property
  `fun X ↦ d X = 0`, viewed through the canonical owners `ObjectProperty.ContainsZero` and
  `ObjectProperty.HasMonoEmbedding`; the source-facing public statements should still speak
  directly about the numerical condition `d X = 0`;
- primitive data: the source-facing zero-object equality `d 0 = 0`, the zero-locus
  mono-embedding owner, and the two numerical inequalities on biproducts and short exact
  sequences;
- derived API: the constant-zero example, the shifted-tail condition on cochain complexes, and the
  final quasi-isomorphic replacement theorem with termwise conclusion `d (L.X n) = 0`.

Source/core/bridge triage:
- `source-facing`: `IsCohomologicalDimensionFunction`,
  `ShiftedDimensionTendsToNegInf`, and the quasi-isomorphic replacement theorem;
- `core/canonical`: `ObjectProperty.ContainsZero`, `ObjectProperty.HasMonoEmbedding`,
  `ShortComplex.ShortExact`, and `QuasiIso`;
- `bridge/view`: the internal zero-locus object property `fun X ↦ d X = 0`, used only where
  `ObjectProperty`-based replacement owners are required.
-/

/-- A cohomological-dimension function on an abelian category is a function to `WithTop ℕ` whose
value on the zero object is zero, whose zero locus, viewed as an object property, has monomorphic
envelopes for all objects, whose value on biproducts is bounded by the maximum of the summand
values, and whose value on the cokernel term of a short exact sequence is bounded by the maximum
of the middle value and one less than the left value. -/
class IsCohomologicalDimensionFunction (d : 𝒜 → WithTop ℕ) : Prop where
  zero_eq : d (0 : 𝒜) = 0
  hasMonoEmbedding : HasMonoEmbedding (fun X ↦ d X = 0)
  biprod_le_max (X Y : 𝒜) : d (X ⊞ Y) ≤ max (d X) (d Y)
  shortExact_right_le_max {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    d S.X₃ ≤ max (d S.X₁ - 1) (d S.X₂)

attribute [instance] IsCohomologicalDimensionFunction.hasMonoEmbedding

namespace IsCohomologicalDimensionFunction

variable {d : 𝒜 → WithTop ℕ} [IsCohomologicalDimensionFunction d]

/-- Helper for Lemma 13.32.1: the zero-dimensional object property attached to `d`. -/
abbrev zeroLocus : ObjectProperty 𝒜 :=
  fun X ↦ d X = 0

/-- The zero object is zero-dimensional for a cohomological-dimension function. -/
theorem prop_zero : d (0 : 𝒜) = 0 := by
  let hd : IsCohomologicalDimensionFunction d := inferInstance
  exact hd.zero_eq

instance zeroLocus_containsZero : ContainsZero (zeroLocus (d := d)) where
  exists_zero := ⟨0, isZero_zero 𝒜, prop_zero⟩

/-- The zero-dimensional objects for a cohomological-dimension function are closed under binary
biproducts. -/
theorem prop_biprod {X Y : 𝒜} (hX : d X = 0) (hY : d Y = 0) :
    d (X ⊞ Y) = 0 := by
  let hd : IsCohomologicalDimensionFunction d := inferInstance
  change d (X ⊞ Y) = 0
  refine le_antisymm ?_ bot_le
  simpa [hX, hY] using hd.biprod_le_max X Y

/-- If the left and middle terms of a short exact sequence are zero-dimensional, then so is the
right term. -/
theorem prop_X₃_of_shortExact {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₁ : d S.X₁ = 0) (h₂ : d S.X₂ = 0) :
    d S.X₃ = 0 := by
  let hd : IsCohomologicalDimensionFunction d := inferInstance
  change d S.X₃ = 0
  refine le_antisymm ?_ bot_le
  simpa [h₁, h₂] using hd.shortExact_right_le_max hS

/-- Helper for Lemma 13.32.1: a cohomological-dimension function is invariant under isomorphism. -/
theorem eq_of_iso {X Y : 𝒜} (e : X ≅ Y) :
    d X = d Y := by
  let hd : IsCohomologicalDimensionFunction d := inferInstance
  let S : ShortComplex 𝒜 :=
    ShortComplex.mk (0 : 0 ⟶ X) e.hom (by simp)
  have hS : S.ShortExact := by
    -- Proof comment: `0 ⟶ X ⟶ Y` is short exact because the second map is an isomorphism.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.exact_iff_mono (S := S) rfl]
      infer_instance
    · infer_instance
    · infer_instance
  have hYX : d Y ≤ d X := by
    -- Proof comment: apply the defining short-exact-sequence inequality to `0 ⟶ X ⟶ Y`.
    simpa [S, hd.zero_eq, max_eq_right bot_le] using hd.shortExact_right_le_max hS
  let T : ShortComplex 𝒜 :=
    ShortComplex.mk (0 : 0 ⟶ Y) e.inv (by simp)
  have hT : T.ShortExact := by
    -- Proof comment: the inverse isomorphism yields the symmetric short exact sequence.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.exact_iff_mono (S := T) rfl]
      infer_instance
    · infer_instance
    · infer_instance
  have hXY : d X ≤ d Y := by
    -- Proof comment: repeat the same estimate for `0 ⟶ Y ⟶ X`.
    simpa [T, hd.zero_eq, max_eq_right bot_le] using hd.shortExact_right_le_max hT
  exact le_antisymm hXY hYX

/-- Helper for Lemma 13.32.1: the zero-dimensional locus `fun X ↦ d X = 0` is closed under
isomorphisms. -/
instance zeroLocus_isClosedUnderIsomorphisms :
    (zeroLocus (d := d)).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    -- Proof comment: rewrite the target along the isomorphism-invariance of `d`.
    change d Y = 0
    change d X = 0 at hX
    rw [← eq_of_iso (d := d) e]
    exact hX

end IsCohomologicalDimensionFunction

/-- The constant-zero function is a cohomological-dimension function. -/
instance instIsCohomologicalDimensionFunctionZero :
    IsCohomologicalDimensionFunction (fun _ : 𝒜 ↦ (0 : WithTop ℕ)) where
  zero_eq := by
    simp
  hasMonoEmbedding := by
    refine ⟨fun X ↦ ?_⟩
    exact ⟨X, by simp, 𝟙 X, inferInstance⟩
  biprod_le_max X Y := by
    simp
  shortExact_right_le_max hS := by
    simp

/-- The shifted dimension function `n + d (K.X n)` tends to `-∞` toward negative degrees when,
for every bound `N`, all sufficiently negative terms have finite `d`-value bounded so that
`n + d (K.X n) ≤ N`. -/
def ShiftedDimensionTendsToNegInf
    (d : 𝒜 → WithTop ℕ) (K : CochainComplex 𝒜 ℤ) : Prop :=
  ∀ N : ℤ, ∃ n₀ : ℤ, ∀ n ≤ n₀, ∃ m : ℕ, d (K.X n) = m ∧ n + m ≤ N

/-- Helper for Lemma 13.32.1: sufficiently far to the left, the shifted-dimension hypothesis
forces the values `d (K.X n)` to be honest natural numbers. -/
theorem eventuallyEqNat_of_shiftedDimensionTendsToNegInf
    {d : 𝒜 → WithTop ℕ} {K : CochainComplex 𝒜 ℤ}
    (hK : ShiftedDimensionTendsToNegInf d K) (N : ℤ) :
    ∃ n₀ : ℤ, ∀ n ≤ n₀, ∃ m : ℕ, d (K.X n) = m := by
  -- Proof comment: unpack the defining bound at the chosen cutoff `N` and forget only the final
  -- inequality `n + m ≤ N`.
  obtain ⟨n₀, hn₀⟩ := hK N
  refine ⟨n₀, ?_⟩
  intro n hn
  obtain ⟨m, hm, _⟩ := hn₀ n hn
  exact ⟨m, hm⟩

/-- Helper for Lemma 13.32.1: choose the natural number realizing a finite value `d (K.X n)`. -/
private noncomputable def natDimensionValue
    {d : 𝒜 → WithTop ℕ} {K : CochainComplex 𝒜 ℤ}
    (hNat : ∀ n : ℤ, ∃ m : ℕ, d (K.X n) = m) (n : ℤ) : ℕ :=
  Classical.choose (hNat n)

/-- Helper for Lemma 13.32.1: the chosen natural number really computes `d (K.X n)`. -/
private theorem natDimensionValue_spec
    {d : 𝒜 → WithTop ℕ} {K : CochainComplex 𝒜 ℤ}
    (hNat : ∀ n : ℤ, ∃ m : ℕ, d (K.X n) = m) (n : ℤ) :
    d (K.X n) = natDimensionValue hNat n := by
  -- Proof comment: unfold the chosen witness from the finiteness hypothesis at degree `n`.
  exact Classical.choose_spec (hNat n)

/-- Helper for Lemma 13.32.1: before any fixed cutoff `a`, the shifted values
`n + d (K.X n)` admit a uniform upper bound once all terms have finite `d`-value. -/
private theorem exists_shiftedDimensionUpperBound_before_cutoff
    {d : 𝒜 → WithTop ℕ} {K : CochainComplex 𝒜 ℤ}
    (hK : ShiftedDimensionTendsToNegInf d K)
    (hNat : ∀ n : ℤ, ∃ m : ℕ, d (K.X n) = m) (a : ℤ) :
    ∃ ξ : ℤ, ∀ n : ℤ, n < a → n + natDimensionValue hNat n ≤ ξ := by
  obtain ⟨n₀, hn₀⟩ := hK 0
  let s : Finset ℤ :=
    (Finset.Icc (n₀ + 1) (a - 1)).image fun n ↦ n + natDimensionValue hNat n
  let ξ : ℤ := if hs : s.Nonempty then max 0 (s.max' hs) else 0
  have hξ_nonneg : 0 ≤ ξ := by
    -- Proof comment: by construction `ξ` is either `0` or `max 0 (...)`.
    dsimp [ξ]
    split_ifs <;> simp
  refine ⟨ξ, ?_⟩
  intro n hna
  by_cases hleft : n ≤ n₀
  · obtain ⟨m, hm, hbound⟩ := hn₀ n hleft
    have hEq : natDimensionValue hNat n = m := by
      -- Proof comment: compare the chosen finite witness with the witness supplied by `hK`.
      have hchosen := natDimensionValue_spec hNat n
      rw [hm] at hchosen
      simpa using hchosen.symm
    calc
      n + natDimensionValue hNat n = n + m := by rw [hEq]
      _ ≤ 0 := hbound
      _ ≤ ξ := hξ_nonneg
  · have hmem : n ∈ Finset.Icc (n₀ + 1) (a - 1) := by
      rw [Finset.mem_Icc]
      omega
    have hs_nonempty : s.Nonempty := by
      refine ⟨n + natDimensionValue hNat n, ?_⟩
      exact Finset.mem_image.mpr ⟨n, hmem, rfl⟩
    have hmax :
        n + natDimensionValue hNat n ≤ s.max' hs_nonempty :=
      Finset.le_max' s _ (Finset.mem_image.mpr ⟨n, hmem, rfl⟩)
    have hξ_eq : ξ = max 0 (s.max' hs_nonempty) := by
      -- Proof comment: once the interval contributes a point, the `if`-branch defining `ξ`
      -- is forced to use the corresponding finite maximum.
      simp [ξ, hs_nonempty]
    calc
      n + natDimensionValue hNat n ≤ s.max' hs_nonempty := hmax
      _ ≤ max 0 (s.max' hs_nonempty) := le_max_right _ _
      _ = ξ := hξ_eq.symm

/-- Helper for Lemma 13.32.1: with a zero-dimensional right tail, the bad shifted values
`n + d (K.X n)` are globally bounded above. -/
private theorem exists_globalBadShiftedDimensionBound
    {d : 𝒜 → WithTop ℕ} {K : CochainComplex 𝒜 ℤ}
    (hK : ShiftedDimensionTendsToNegInf d K)
    (hNat : ∀ n : ℤ, ∃ m : ℕ, d (K.X n) = m)
    (hTail : ∃ a : ℤ, ∀ n : ℤ, a ≤ n → d (K.X n) = 0) :
    ∃ ξ : ℤ, ∀ n : ℤ, d (K.X n) ≠ 0 → n + natDimensionValue hNat n ≤ ξ := by
  rcases hTail with ⟨a, ha⟩
  obtain ⟨ξ, hξ⟩ := exists_shiftedDimensionUpperBound_before_cutoff hK hNat a
  refine ⟨ξ, ?_⟩
  intro n hn
  by_cases hna : n < a
  · exact hξ n hna
  · have hge : a ≤ n := by omega
    exact False.elim (hn (ha n hge))

/-- Helper for Lemma 13.32.1: if some term is not yet zero-dimensional, then the textbook
quantity `ξ(K) = max {n + d(K.X n)}` for bad degrees has a realized greatest value. -/
private theorem exists_badShiftedDimensionMaximizer
    {d : 𝒜 → WithTop ℕ} {K : CochainComplex 𝒜 ℤ}
    (hK : ShiftedDimensionTendsToNegInf d K)
    (hNat : ∀ n : ℤ, ∃ m : ℕ, d (K.X n) = m)
    (hTail : ∃ a : ℤ, ∀ n : ℤ, a ≤ n → d (K.X n) = 0)
    (hBad : ∃ n : ℤ, d (K.X n) ≠ 0) :
    ∃ ξ n : ℤ, d (K.X n) ≠ 0 ∧ ξ = n + natDimensionValue hNat n ∧
      ∀ m : ℤ, d (K.X m) ≠ 0 → m + natDimensionValue hNat m ≤ ξ := by
  obtain ⟨ξBound, hBound⟩ := exists_globalBadShiftedDimensionBound hK hNat hTail
  let S : Set ℤ := {x | ∃ n : ℤ, d (K.X n) ≠ 0 ∧ x = n + natDimensionValue hNat n}
  have hBdd : BddAbove S := by
    refine ⟨ξBound, ?_⟩
    intro x hx
    rcases hx with ⟨n, hn, rfl⟩
    exact hBound n hn
  have hNonempty : S.Nonempty := by
    rcases hBad with ⟨n, hn⟩
    exact ⟨n + natDimensionValue hNat n, n, hn, rfl⟩
  obtain ⟨ξ, hξ⟩ := BddAbove.exists_isGreatest_of_nonempty hBdd hNonempty
  rcases hξ.1 with ⟨n, hn, hEq⟩
  refine ⟨ξ, n, hn, hEq, ?_⟩
  intro m hm
  exact hξ.2 ⟨m, hm, rfl⟩

namespace IsCohomologicalDimensionFunction

variable {d : 𝒜 → WithTop ℕ} [IsCohomologicalDimensionFunction d]

/-- Helper for Lemma 13.32.1: the cokernel term occurring in one elementary replacement satisfies
the textbook dimension estimate. -/
theorem cokernelBiprodLift_le_max
    {X Y M : 𝒜} (ι : X ⟶ M) [Mono ι] (f : X ⟶ Y) (hM : d M = 0) :
    d (cokernel (biprod.lift ι f)) ≤ max (d X - 1) (d Y) := by
  let hd : IsCohomologicalDimensionFunction d := inferInstance
  let S : ShortComplex 𝒜 :=
    ShortComplex.mk (biprod.lift ι f) (cokernel.π (biprod.lift ι f)) (by simp)
  have hS : S.ShortExact := by
    -- Proof comment: the cokernel row of a monomorphism is the standard short exact sequence.
    exact
      ShortComplex.ShortExact.mk'
        (ShortComplex.exact_cokernel (biprod.lift ι f))
        inferInstance
        inferInstance
  have hCok :
      d (cokernel (biprod.lift ι f)) ≤ max (d X - 1) (d (M ⊞ Y)) := by
    -- Proof comment: apply the defining short-exact-sequence inequality to the elementary row.
    simpa [S] using hd.shortExact_right_le_max hS
  have hBiprod : d (M ⊞ Y) ≤ d Y := by
    -- Proof comment: the middle term is `M ⊞ Y`, and the zero-dimensional hypothesis on `M`
    -- collapses the biproduct estimate to the bound by `d Y`.
    simpa [hM, max_eq_right bot_le] using hd.biprod_le_max M Y
  exact le_trans hCok (max_le_max le_rfl hBiprod)

/-- Helper for Lemma 13.32.1: if both neighboring terms are already zero-dimensional, then one
elementary replacement keeps the new cokernel term zero-dimensional as well. -/
theorem cokernelBiprodLift_eq_zero
    {X Y M : 𝒜} (ι : X ⟶ M) [Mono ι] (f : X ⟶ Y)
    (hX : d X = 0) (hY : d Y = 0) (hM : d M = 0) :
    d (cokernel (biprod.lift ι f)) = 0 := by
  -- Proof comment: specialize the one-step inequality to the zero-dimensional case and use
  -- `bot_le` for the reverse inequality.
  refine le_antisymm ?_ bot_le
  simpa [hX, hY] using cokernelBiprodLift_le_max (d := d) ι f hM

end IsCohomologicalDimensionFunction

/- Proof sketch: once a complex already has a zero-dimensional right tail and finite
cohomological-dimension values in every degree, the remaining source-faithful work is the
finite-window `ξ`-descent by elementary replacements together with the eventual-stability
realization. -/
/-- Helper for Lemma 13.32.1: if a chain map `β : K ⟶ I` lands in a complex that is strictly
`≥ a`, then the cutoff composite `K.d (a - 1) a ≫ β.f a` is forced to vanish. -/
private theorem cutoff_comp_eq_zero_of_isStrictlyGE
    {K I : CochainComplex 𝒜 ℤ} (a : ℤ) (β : K ⟶ I) [I.IsStrictlyGE a] :
    K.d (a - 1) a ≫ β.f a = 0 := by
  have hβPrev : β.f (a - 1) = 0 := by
    -- Proof comment: the target term in degree `a - 1` vanishes, so every morphism into it is
    -- zero.
    exact (CochainComplex.isZero_of_isStrictlyGE I a (a - 1) (by omega)).eq_of_tgt _ _
  -- Proof comment: the chain-map square at the cutoff identifies the desired composite with the
  -- zero morphism through the vanished previous component.
  calc
    K.d (a - 1) a ≫ β.f a = β.f (a - 1) ≫ I.d (a - 1) a := by
      simpa using (β.comm (a - 1) a).symm
    _ = 0 := by simp [hβPrev]

/-- Helper for Lemma 13.32.1: on retained degrees of the lower brutal truncation, the truncated
term canonically identifies with the original term of `K`. -/
private noncomputable def lowerStupidTruncationXIso
    {K : CochainComplex 𝒜 ℤ} (a : ℤ) {n : ℤ} (han : a ≤ n) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntGE a)).X n ≅ K.X n :=
  K.stupidTruncXIso (ComplexShape.embeddingUpIntGE a)
    (embeddingUpIntGE_toNat_sub_eq a n han)

/-- Helper for Lemma 13.32.1: after transporting along the retained lower-truncation
identifications, the lower brutal truncation differential agrees with that of `K`. -/
private theorem lowerStupidTruncation_d_via_xIso
    {K : CochainComplex 𝒜 ℤ} (a : ℤ) {i j : ℤ}
    (hai : a ≤ i) (haj : a ≤ j) :
    (lowerStupidTruncationXIso (K := K) a hai).inv ≫
        (K.stupidTrunc (ComplexShape.embeddingUpIntGE a)).d i j ≫
        (lowerStupidTruncationXIso (K := K) a haj).hom =
      K.d i j := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ) :=
    ComplexShape.embeddingUpIntGE a
  let i₀ : ℕ := Int.toNat (i - a)
  let j₀ : ℕ := Int.toNat (j - a)
  have hi₀ : e.f i₀ = i := embeddingUpIntGE_toNat_sub_eq a i hai
  have hj₀ : e.f j₀ = j := embeddingUpIntGE_toNat_sub_eq a j haj
  -- Proof comment: read the stupid truncation as `restriction` followed by `extend`, then peel
  -- both constructions away to recover the ambient differential.
  change (lowerStupidTruncationXIso (K := K) a hai).inv ≫
      ((K.restriction e).extend e).d i j ≫
      (lowerStupidTruncationXIso (K := K) a haj).hom =
        K.d i j
  rw [HomologicalComplex.extend_d_eq (K := K.restriction e) (e := e) hi₀ hj₀]
  rw [HomologicalComplex.restriction_d_eq (K := K) (e := e) hi₀ hj₀]
  simp [lowerStupidTruncationXIso, HomologicalComplex.stupidTrunc,
    HomologicalComplex.stupidTruncXIso, HomologicalComplex.restrictionXIso, e, i₀, j₀]

/-- Helper for Lemma 13.32.1: the lower brutal truncation carries a canonical inclusion into the
original complex. -/
private noncomputable def lowerStupidTruncationInclusion
    (K : CochainComplex 𝒜 ℤ) (a : ℤ) :
    K.stupidTrunc (ComplexShape.embeddingUpIntGE a) ⟶ K where
  f n :=
    if han : a ≤ n then
      (lowerStupidTruncationXIso (K := K) a han).hom
    else
      0
  comm' i j hij := by
    by_cases hai : a ≤ i
    · have haj : a ≤ j := by
        have hj : j = i + 1 := by
          simpa [ComplexShape.up, eq_comm] using hij
        omega
      rw [dif_pos hai, dif_pos haj]
      calc
        (lowerStupidTruncationXIso (K := K) a hai).hom ≫ K.d i j =
            (lowerStupidTruncationXIso (K := K) a hai).hom ≫
              ((lowerStupidTruncationXIso (K := K) a hai).inv ≫
                (K.stupidTrunc (ComplexShape.embeddingUpIntGE a)).d i j ≫
                  (lowerStupidTruncationXIso (K := K) a haj).hom) := by
              rw [lowerStupidTruncation_d_via_xIso (K := K) a hai haj]
        _ = (K.stupidTrunc (ComplexShape.embeddingUpIntGE a)).d i j ≫
              (lowerStupidTruncationXIso (K := K) a haj).hom := by
              simp [Category.assoc]
    · have hzero :
          IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntGE a)).X i) := by
        -- Proof comment: below the cutoff, the lower brutal truncation vanishes by construction.
        exact K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE a) i
          (by
            simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using lt_of_not_ge hai)
      by_cases haj : a ≤ j
      · have hsrc :
            (K.stupidTrunc (ComplexShape.embeddingUpIntGE a)).d i j = 0 :=
          hzero.eq_of_src ((K.stupidTrunc (ComplexShape.embeddingUpIntGE a)).d i j) 0
        simp [lowerStupidTruncationInclusion, hai, haj, hsrc]
      · simp [lowerStupidTruncationInclusion, hai, haj]

/-- Helper for Lemma 13.32.1: on retained degrees of the upper brutal truncation, the truncated
term canonically identifies with the original term of `K`. -/
private noncomputable def upperStupidTruncationXIso
    {K : CochainComplex 𝒜 ℤ} (a : ℤ) {n : ℤ} (hna : n ≤ a) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).X n ≅ K.X n := by
  let j : ℕ := Int.toNat (a - n)
  have hj : (ComplexShape.embeddingUpIntLE a).f j = n :=
    embeddingUpIntLE_toNat_sub_eq a n hna
  exact K.stupidTruncXIso (ComplexShape.embeddingUpIntLE a) hj

/-- Helper for Lemma 13.32.1: after transporting along the retained upper-truncation
identifications, the upper brutal truncation differential agrees with that of `K`. -/
private theorem upperStupidTruncation_d_via_xIso
    {K : CochainComplex 𝒜 ℤ} (a : ℤ) {i j : ℤ}
    (hia : i ≤ a) (hja : j ≤ a) :
    (upperStupidTruncationXIso (K := K) a hia).inv ≫
        (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).d i j ≫
        (upperStupidTruncationXIso (K := K) a hja).hom =
      K.d i j := by
  let e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ) :=
    ComplexShape.embeddingUpIntLE a
  let i₀ : ℕ := Int.toNat (a - i)
  let j₀ : ℕ := Int.toNat (a - j)
  have hi₀ : e.f i₀ = i := embeddingUpIntLE_toNat_sub_eq a i hia
  have hj₀ : e.f j₀ = j := embeddingUpIntLE_toNat_sub_eq a j hja
  -- Proof comment: read the stupid truncation as `restriction` followed by `extend`, then peel
  -- both constructions away to recover the ambient differential.
  change (upperStupidTruncationXIso (K := K) a hia).inv ≫
      ((K.restriction e).extend e).d i j ≫
      (upperStupidTruncationXIso (K := K) a hja).hom =
        K.d i j
  rw [HomologicalComplex.extend_d_eq (K := K.restriction e) (e := e) hi₀ hj₀]
  rw [HomologicalComplex.restriction_d_eq (K := K) (e := e) hi₀ hj₀]
  simp [upperStupidTruncationXIso, HomologicalComplex.stupidTrunc,
    HomologicalComplex.stupidTruncXIso, HomologicalComplex.restrictionXIso, e, i₀, j₀]

/-- Helper for Lemma 13.32.1: the upper brutal truncation carries a canonical projection from the
original complex. -/
private noncomputable def upperStupidTruncationProjection
    (K : CochainComplex 𝒜 ℤ) (a : ℤ) :
    K ⟶ K.stupidTrunc (ComplexShape.embeddingUpIntLE a) where
  f n :=
    if hna : n ≤ a then
      (upperStupidTruncationXIso (K := K) a hna).inv
    else
      0
  comm' i j hij := by
    by_cases hia : i ≤ a
    · have hja : j ≤ a := by
        have hj : j = i + 1 := by
          simpa [ComplexShape.up, eq_comm] using hij
        omega
      rw [dif_pos hia, dif_pos hja]
      have hdiff :
          (upperStupidTruncationXIso (K := K) a hia).inv ≫
              (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).d i j =
            K.d i j ≫ (upperStupidTruncationXIso (K := K) a hja).inv := by
        -- Proof comment: postcompose the transported differential identity with the inverse of
        -- the target-degree identification.
        have h :=
          upperStupidTruncation_d_via_xIso (K := K) a hia hja
        have h' := congrArg
          (fun f ↦ f ≫ (upperStupidTruncationXIso (K := K) a hja).inv) h
        simpa [Category.assoc] using h'
      simpa [Category.assoc] using hdiff.symm
    · have hja : ¬ j ≤ a := by
        have hj : j = i + 1 := by
          simpa [ComplexShape.up, eq_comm] using hij
        omega
      simp [upperStupidTruncationProjection, hia, hja]

/-- Helper for Lemma 13.32.1: the brutal cut
`σ_{≥ a}K ⟶ K ⟶ σ_{≤ a - 1}K` composes to zero. -/
private theorem stupidTruncationCut_comp_zero
    (K : CochainComplex 𝒜 ℤ) (a : ℤ) :
    lowerStupidTruncationInclusion K a ≫ upperStupidTruncationProjection K (a - 1) = 0 := by
  ext n
  by_cases hna : n ≤ a - 1
  · have hnot : ¬ a ≤ n := by omega
    simp [HomologicalComplex.comp_f, lowerStupidTruncationInclusion,
      upperStupidTruncationProjection, hna, hnot]
  · simp [HomologicalComplex.comp_f, lowerStupidTruncationInclusion,
    upperStupidTruncationProjection, hna]

/-- Helper for Lemma 13.32.1: the canonical brutal cut
`σ_{≥ a}K ⟶ K ⟶ σ_{≤ a - 1}K` packaged as a short complex. -/
private noncomputable def stupidTruncationCutShortComplex
    (K : CochainComplex 𝒜 ℤ) (a : ℤ) :
    ShortComplex (CochainComplex 𝒜 ℤ) :=
  ShortComplex.mk
    (lowerStupidTruncationInclusion K a)
    (upperStupidTruncationProjection K (a - 1))
    (stupidTruncationCut_comp_zero K a)

/-- Helper for Lemma 13.32.1: every degree of the brutal cut short complex splits, with one outer
term zero below the cutoff and the other zero on and above it. -/
private theorem stupidTruncationCut_degreewiseSplitting
    (K : CochainComplex 𝒜 ℤ) (a n : ℤ) :
    ((stupidTruncationCutShortComplex K a).map
      (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)).Splitting := by
  let S :=
    (stupidTruncationCutShortComplex K a).map
      (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)
  by_cases hna : n ≤ a - 1
  · change S.Splitting
    have hX₁ : IsZero S.X₁ := by
      -- Proof comment: below the cutoff, the lower brutal truncation vanishes.
      dsimp [S, stupidTruncationCutShortComplex]
      exact K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE a) n
        (by simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using lt_of_lt_of_le
          (by omega : n < a) le_rfl)
    have hg : IsIso S.g := by
      -- Proof comment: on the retained upper range, the projection is the transported identity.
      dsimp [S, stupidTruncationCutShortComplex, upperStupidTruncationProjection]
      rw [dif_pos hna]
      infer_instance
    exact ShortComplex.Splitting.ofIsZeroOfIsIso S hX₁ hg
  · change S.Splitting
    have hX₃ : IsZero S.X₃ := by
      -- Proof comment: on and above the cutoff, the upper brutal truncation vanishes.
      dsimp [S, stupidTruncationCutShortComplex]
      exact K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntLE (a - 1)) n
        (by
          intro m hm
          dsimp [ComplexShape.embeddingUpIntLE] at hm
          omega)
    have hf : IsIso S.f := by
      -- Proof comment: on the retained lower range, the inclusion is the transported identity.
      dsimp [S, stupidTruncationCutShortComplex, lowerStupidTruncationInclusion]
      have han : a ≤ n := by omega
      rw [dif_pos han]
      infer_instance
    exact ShortComplex.Splitting.ofIsIsoOfIsZero S hf hX₃

/-- Helper for Lemma 13.32.1: the canonical brutal cut
`σ_{≥ a}K ⟶ K ⟶ σ_{≤ a - 1}K` is short exact. -/
private theorem stupidTruncationCut_shortExact
    (K : CochainComplex 𝒜 ℤ) (a : ℤ) :
    (stupidTruncationCutShortComplex K a).ShortExact := by
  -- Proof comment: evaluate degreewise and use the canonical split models in the two cutoff
  -- regions.
  exact HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n ↦ (stupidTruncationCut_degreewiseSplitting K a n).shortExact)

/-- Helper for Lemma 13.32.1: the explicit splice object uses `K` below the cutoff `a` and `I`
from degree `a` onward. -/
private abbrev resolvedZeroTailSpliceX
    {K I : CochainComplex 𝒜 ℤ} (a : ℤ) (n : ℤ) : 𝒜 :=
  if n < a then K.X n else I.X n

/-- Helper for Lemma 13.32.1: the splice differential is inherited from `K` below `a`, inherited
from `I` on and above `a`, and at the cutoff uses the comparison map `β`. -/
private noncomputable def resolvedZeroTailSpliceD
    {K I : CochainComplex 𝒜 ℤ} (a : ℤ) (β : K ⟶ I) (n : ℤ) :
    resolvedZeroTailSpliceX (K := K) (I := I) a n ⟶
      resolvedZeroTailSpliceX (K := K) (I := I) a (n + 1) :=
  by
    by_cases hnext : n + 1 < a
    · have hn : n < a := by omega
      simpa [resolvedZeroTailSpliceX, hn, hnext] using (K.d n (n + 1))
    · by_cases hn : n < a
      · simpa [resolvedZeroTailSpliceX, hn, hnext] using (K.d n (n + 1) ≫ β.f (n + 1))
      · simpa [resolvedZeroTailSpliceX, hn, hnext] using (I.d n (n + 1))

/-- Helper for Lemma 13.32.1: if a composable pair of morphisms has zero composite, then the same
remains true after transporting source and target objects along equalities. -/
private theorem cast_comp_eq_zero
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : 𝒜}
    (h₁ : X₁ = Y₁) (h₂ : X₂ = Y₂) (h₃ : X₃ = Y₃)
    (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) (hfg : f ≫ g = 0) :
    cast (by cases h₁; cases h₂; rfl) f ≫
        cast (by cases h₂; cases h₃; rfl) g = 0 := by
  subst h₁
  subst h₂
  subst h₃
  simpa using hfg

/-- Helper for Lemma 13.32.1: transporting a morphism into the splice's dependent object family
commutes with the canonical `eqToHom` comparison maps. -/
private theorem eqToHom_comp_cast
    {X₁ X₂ Y₁ Y₂ : 𝒜}
    (h₁ : X₁ = Y₁) (h₂ : X₂ = Y₂) (f : X₁ ⟶ X₂) :
    eqToHom h₁ ≫ cast (by cases h₁; cases h₂; rfl) f = f ≫ eqToHom h₂ := by
  subst h₁
  subst h₂
  simp

/-- Helper for Lemma 13.32.1: the explicit splice differential squares to zero. -/
private theorem resolvedZeroTailSpliceSq
    {K I : CochainComplex 𝒜 ℤ} (a : ℤ) (β : K ⟶ I) (n : ℤ) :
    resolvedZeroTailSpliceD (K := K) (I := I) a β n ≫
        resolvedZeroTailSpliceD (K := K) (I := I) a β (n + 1) = 0 := by
  by_cases hnext : n + 1 < a
  · have hn : n < a := by omega
    by_cases hnext' : n + 2 < a
    · -- Proof comment: strictly below the cutoff, both splice differentials come from `K`.
      have hnext₂ : n + 1 + 1 < a := by omega
      have h₁ : resolvedZeroTailSpliceX (K := K) (I := I) a n = K.X n := by
        simp [resolvedZeroTailSpliceX, hn]
      have h₂ : resolvedZeroTailSpliceX (K := K) (I := I) a (n + 1) = K.X (n + 1) := by
        simp [resolvedZeroTailSpliceX, hnext]
      have h₃ :
          resolvedZeroTailSpliceX (K := K) (I := I) a (n + 1 + 1) = K.X (n + 1 + 1) := by
        simp [resolvedZeroTailSpliceX, hnext₂]
      -- Proof comment: after fixing the object identifications, this is exactly `K.d_comp_d`.
      simpa [resolvedZeroTailSpliceD, hn, hnext, hnext', hnext₂] using
        cast_comp_eq_zero h₁ h₂ h₃
          (K.d n (n + 1)) (K.d (n + 1) (n + 1 + 1)) (K.d_comp_d n (n + 1) (n + 1 + 1))
    · -- Proof comment: at the cutoff, the second differential is the `β`-bridge into `I`.
      have hnext₂ : ¬ n + 1 + 1 < a := by omega
      have h₁ : resolvedZeroTailSpliceX (K := K) (I := I) a n = K.X n := by
        simp [resolvedZeroTailSpliceX, hn]
      have h₂ : resolvedZeroTailSpliceX (K := K) (I := I) a (n + 1) = K.X (n + 1) := by
        simp [resolvedZeroTailSpliceX, hnext]
      have h₃ :
          resolvedZeroTailSpliceX (K := K) (I := I) a (n + 1 + 1) = I.X (n + 1 + 1) := by
        simp [resolvedZeroTailSpliceX, hnext₂]
      have hfg :
          K.d n (n + 1) ≫ (K.d (n + 1) (n + 1 + 1) ≫ β.f (n + 1 + 1)) = 0 := by
        calc
          K.d n (n + 1) ≫ (K.d (n + 1) (n + 1 + 1) ≫ β.f (n + 1 + 1)) =
              (K.d n (n + 1) ≫ K.d (n + 1) (n + 1 + 1)) ≫ β.f (n + 1 + 1) := by
                rw [Category.assoc]
          _ = 0 := by simp [K.d_comp_d]
      -- Proof comment: the only new transport is the cutoff target, and the core composite still
      -- dies by `K.d_comp_d`.
      simpa [resolvedZeroTailSpliceD, hn, hnext, hnext', hnext₂, Category.assoc] using
        cast_comp_eq_zero h₁ h₂ h₃
          (K.d n (n + 1)) (K.d (n + 1) (n + 1 + 1) ≫ β.f (n + 1 + 1)) hfg
  · by_cases hn : n < a
    · -- Proof comment: this is the unique cutoff-crossing regime, so use the chain-map square
      -- for `β` and then the square-zero relation on `K`.
      have hnext' : ¬ n + 2 < a := by omega
      have hnext₂ : ¬ n + 1 + 1 < a := by omega
      have h₁ : resolvedZeroTailSpliceX (K := K) (I := I) a n = K.X n := by
        simp [resolvedZeroTailSpliceX, hn]
      have h₂ : resolvedZeroTailSpliceX (K := K) (I := I) a (n + 1) = I.X (n + 1) := by
        simp [resolvedZeroTailSpliceX, hnext]
      have h₃ :
          resolvedZeroTailSpliceX (K := K) (I := I) a (n + 1 + 1) = I.X (n + 1 + 1) := by
        simp [resolvedZeroTailSpliceX, hnext₂]
      have hfg : (K.d n (n + 1) ≫ β.f (n + 1)) ≫ I.d (n + 1) (n + 1 + 1) = 0 := by
        calc
          (K.d n (n + 1) ≫ β.f (n + 1)) ≫ I.d (n + 1) (n + 1 + 1) =
              K.d n (n + 1) ≫ (β.f (n + 1) ≫ I.d (n + 1) (n + 1 + 1)) := by
                rw [Category.assoc]
          _ = K.d n (n + 1) ≫ (K.d (n + 1) (n + 1 + 1) ≫ β.f (n + 1 + 1)) := by
                rw [(β.comm (n + 1) (n + 1 + 1)).symm]
          _ = (K.d n (n + 1) ≫ K.d (n + 1) (n + 1 + 1)) ≫ β.f (n + 1 + 1) := by
                rw [Category.assoc]
          _ = 0 := by simp [K.d_comp_d]
      -- Proof comment: the cutoff-crossing composite is transported from the chain-map square for
      -- `β` followed by `K.d_comp_d`.
      simpa [resolvedZeroTailSpliceD, hn, hnext, hnext', hnext₂, Category.assoc] using
        cast_comp_eq_zero h₁ h₂ h₃
          (K.d n (n + 1) ≫ β.f (n + 1)) (I.d (n + 1) (n + 1 + 1)) hfg
    · -- Proof comment: on and above the cutoff, both splice differentials are those of `I`.
      have hnext' : ¬ n + 2 < a := by omega
      have hnext₂ : ¬ n + 1 + 1 < a := by omega
      have h₁ : resolvedZeroTailSpliceX (K := K) (I := I) a n = I.X n := by
        simp [resolvedZeroTailSpliceX, hn]
      have h₂ : resolvedZeroTailSpliceX (K := K) (I := I) a (n + 1) = I.X (n + 1) := by
        simp [resolvedZeroTailSpliceX, hnext]
      have h₃ :
          resolvedZeroTailSpliceX (K := K) (I := I) a (n + 1 + 1) = I.X (n + 1 + 1) := by
        simp [resolvedZeroTailSpliceX, hnext₂]
      -- Proof comment: above the cutoff, the splice is literally the complex `I`.
      simpa [resolvedZeroTailSpliceD, hn, hnext, hnext', hnext₂] using
        cast_comp_eq_zero h₁ h₂ h₃
          (I.d n (n + 1)) (I.d (n + 1) (n + 1 + 1)) (I.d_comp_d n (n + 1) (n + 1 + 1))

/-- Helper for Lemma 13.32.1: the explicit splice complex glued from `K` and `I` along `β`. -/
private noncomputable def resolvedZeroTailSplice
    {K I : CochainComplex 𝒜 ℤ} (a : ℤ) (β : K ⟶ I) :
    CochainComplex 𝒜 ℤ :=
  CochainComplex.of
    (resolvedZeroTailSpliceX (K := K) (I := I) a)
    (resolvedZeroTailSpliceD (K := K) (I := I) a β)
    (resolvedZeroTailSpliceSq (K := K) (I := I) a β)

/-- Helper for Lemma 13.32.1: below the cutoff, the splice term is literally the original term of
`K`. -/
private theorem resolvedZeroTailSplice_X_of_lt
    {K I : CochainComplex 𝒜 ℤ} (a : ℤ) (β : K ⟶ I) {n : ℤ} (hn : n < a) :
    (resolvedZeroTailSplice (K := K) (I := I) a β).X n = K.X n := by
  simp [resolvedZeroTailSplice, resolvedZeroTailSpliceX, hn]

/-- Helper for Lemma 13.32.1: on and above the cutoff, the splice term is literally the resolving
term of `I`. -/
private theorem resolvedZeroTailSplice_X_of_ge
    {K I : CochainComplex 𝒜 ℤ} (a : ℤ) (β : K ⟶ I) {n : ℤ} (hn : a ≤ n) :
    (resolvedZeroTailSplice (K := K) (I := I) a β).X n = I.X n := by
  have hnot : ¬ n < a := by omega
  simp [resolvedZeroTailSplice, resolvedZeroTailSpliceX, hnot]

/-- Helper for Lemma 13.32.1: splicing in a resolved right tail does not change the left-hand
decay condition `n + d(K.X n) → -∞`. -/
private theorem shiftedDimensionTendsToNegInf_resolvedZeroTailSplice
    {d : 𝒜 → WithTop ℕ} {K I : CochainComplex 𝒜 ℤ}
    (a : ℤ) (β : K ⟶ I) (hK : ShiftedDimensionTendsToNegInf d K) :
    ShiftedDimensionTendsToNegInf d (resolvedZeroTailSplice (K := K) (I := I) a β) := by
  intro N
  obtain ⟨n₀, hn₀⟩ := hK N
  refine ⟨min n₀ (a - 1), ?_⟩
  intro n hn
  have hna : n < a := by
    omega
  obtain ⟨m, hm, hmN⟩ := hn₀ n (le_trans hn (Int.min_le_left _ _))
  refine ⟨m, ?_, hmN⟩
  simpa [resolvedZeroTailSplice, resolvedZeroTailSpliceX, hna] using hm

/-- Helper for Lemma 13.32.1: if the left tail already has finite `d`-values and the spliced-in
right tail has `d = 0`, then every splice term has a finite `d`-value. -/
private theorem resolvedZeroTailSplice_natValued_of_leftNat
    {d : 𝒜 → WithTop ℕ} {K I : CochainComplex 𝒜 ℤ}
    (a : ℤ) (β : K ⟶ I)
    (hLeft : ∀ n : ℤ, n < a → ∃ m : ℕ, d (K.X n) = m)
    (hRight : ∀ n : ℤ, d (I.X n) = 0) :
    ∀ n : ℤ, ∃ m : ℕ, d ((resolvedZeroTailSplice (K := K) (I := I) a β).X n) = m := by
  intro n
  by_cases hn : n < a
  · -- Proof comment: below the cutoff, reuse the finite-value witness on the original left tail.
    rcases hLeft n hn with ⟨m, hm⟩
    exact ⟨m, by simpa [resolvedZeroTailSplice, resolvedZeroTailSpliceX, hn] using hm⟩
  · -- Proof comment: on the resolved right tail, every term already has `d = 0`.
    refine ⟨0, ?_⟩
    simpa [resolvedZeroTailSplice, resolvedZeroTailSpliceX, hn] using hRight n

/-- Helper for Lemma 13.32.1: the explicit splice inherits the zero-dimensional right tail of the
resolved complex `I`. -/
private theorem resolvedZeroTailSplice_zeroTail
    {d : 𝒜 → WithTop ℕ} {K I : CochainComplex 𝒜 ℤ}
    (a : ℤ) (β : K ⟶ I) (hRight : ∀ n : ℤ, d (I.X n) = 0) :
    ∀ n : ℤ, a ≤ n → d ((resolvedZeroTailSplice (K := K) (I := I) a β).X n) = 0 := by
  intro n hn
  have hnot : ¬ n < a := by omega
  simpa [resolvedZeroTailSplice, resolvedZeroTailSpliceX, hnot] using hRight n

/-- Helper for Lemma 13.32.1: the comparison map into the spliced complex is the identity below
the cutoff and the given map `β` on and above the cutoff. -/
private noncomputable def resolvedZeroTailSpliceMap
    {K I : CochainComplex 𝒜 ℤ} (a : ℤ) (β : K ⟶ I) :
    K ⟶ resolvedZeroTailSplice (K := K) (I := I) a β :=
  { f := fun n ↦
      if hn : n < a then
        by
          -- Proof comment: below the cutoff the splice reuses the original term of `K`, so the
          -- comparison component is literally the identity.
          simpa [resolvedZeroTailSplice, resolvedZeroTailSpliceX, hn]
            using (𝟙 (K.X n))
      else
        by
          -- Proof comment: on and above the cutoff the splice term is the resolving term of `I`,
          -- so we reuse the corresponding component of `β`.
          simpa [resolvedZeroTailSplice, resolvedZeroTailSpliceX, hn]
            using (β.f n)
    comm' := fun i j hij ↦ by
      have hsucc : i + 1 = j := by simpa using hij
      subst j
      by_cases hnext : i + 1 < a
      · have hi : i < a := by omega
        -- Proof comment: strictly below the cutoff all comparison components are identities.
        have h₁ : K.X i = resolvedZeroTailSpliceX (K := K) (I := I) a i := by
          simp [resolvedZeroTailSpliceX, hi]
        have h₂ : K.X (i + 1) = resolvedZeroTailSpliceX (K := K) (I := I) a (i + 1) := by
          simp [resolvedZeroTailSpliceX, hnext]
        simpa [resolvedZeroTailSplice, resolvedZeroTailSpliceD, hi, hnext] using
          eqToHom_comp_cast h₁ h₂ (K.d i (i + 1))
      · by_cases hi : i < a
        · -- Proof comment: at the cutoff the target differential is `K.d ≫ β`, matching the two
          -- chosen comparison components.
          have h₁ : K.X i = resolvedZeroTailSpliceX (K := K) (I := I) a i := by
            simp [resolvedZeroTailSpliceX, hi]
          have h₂ : I.X (i + 1) = resolvedZeroTailSpliceX (K := K) (I := I) a (i + 1) := by
            simp [resolvedZeroTailSpliceX, hnext]
          simpa [resolvedZeroTailSplice, resolvedZeroTailSpliceD, hi, hnext] using
            eqToHom_comp_cast h₁ h₂ (K.d i (i + 1) ≫ β.f (i + 1))
        · -- Proof comment: on and above the cutoff the splice differential is exactly the one of
          -- `I`, so the chain map identity is inherited from `β`.
          have h₁ : I.X i = resolvedZeroTailSpliceX (K := K) (I := I) a i := by
            simp [resolvedZeroTailSpliceX, hi]
          have h₂ : I.X (i + 1) = resolvedZeroTailSpliceX (K := K) (I := I) a (i + 1) := by
            simp [resolvedZeroTailSpliceX, hnext]
          simpa [resolvedZeroTailSplice, resolvedZeroTailSpliceD, hi, hnext, Category.assoc,
            eqToHom_comp_cast h₁ h₂ (I.d i (i + 1))] using β.comm i (i + 1) }

/-- Helper for Lemma 13.32.1: if a morphism is a quasi-isomorphism in every degree on and above
the cutoff, then the induced splice comparison map is a quasi-isomorphism. -/
private theorem resolvedZeroTailSpliceMap_quasiIso
    {K I : CochainComplex 𝒜 ℤ} (a : ℤ) (β : K ⟶ I)
    (hβ : ∀ n : ℤ, a ≤ n → QuasiIsoAt β n) :
    QuasiIso (resolvedZeroTailSpliceMap (K := K) (I := I) a β) := by
  -- TODO: the old truncation-interface plan assumed the front-end replacement came from the
  -- source-style stupid truncation. In the current file `β` is built from smart `truncGE`, so as
  -- soon as the target tail is strictly `≥ a`, `cutoff_comp_eq_zero_of_isStrictlyGE` forces the
  -- cutoff differential `K.d (a - 1) a ≫ β.f a` to vanish. This means the present splice glues in
  -- the smart truncation tail rather than the source proof's tail, so the right next pivot is to
  -- build the resolved replacement from `stupidTrunc` (or an equivalent owner API) before trying
  -- to finish the quasi-isomorphism proof.
  sorry

/-- Helper for Lemma 13.32.1: after replacing the right tail by zero-dimensional terms and
eliminating all `∞`-values, the only remaining task is the textbook `ξ`-descent that performs
elementary replacements until every degree has `d = 0`. -/
private theorem exists_quasiIso_to_termwise_zero_dimension_of_natValued_and_eventually_zero
    (d : 𝒜 → WithTop ℕ) [IsCohomologicalDimensionFunction d] (K : CochainComplex 𝒜 ℤ)
    (hK : ShiftedDimensionTendsToNegInf d K)
    (hNat : ∀ n : ℤ, ∃ m : ℕ, d (K.X n) = m)
    (hTail : ∃ a : ℤ, ∀ n : ℤ, a ≤ n → d (K.X n) = 0) :
    ∃ (L : CochainComplex 𝒜 ℤ) (α : K ⟶ L), QuasiIso α ∧
      ∀ n : ℤ, d (L.X n) = 0 := by
  -- Proof comment: the eventual-zero-tail descent is isolated in this theorem, so the front-end
  -- wrapper below no longer depends on a forward reference while the remaining source-faithful
  -- descent proof is repaired.
  -- TODO: after the front-end pivot to the correct resolved replacement, this theorem should
  -- carry the textbook `ξ`-descent by elementary replacements and eventual stabilization.
  sorry

/-- Helper for Lemma 13.32.1: once a quasi-isomorphic replacement with finite `d`-values and a
zero-dimensional right tail is available, the theorem reduces to the isolated `ξ`-descent. -/
private theorem exists_quasiIso_to_termwise_zero_dimension_of_resolvedZeroTailReplacement
    (d : 𝒜 → WithTop ℕ) [IsCohomologicalDimensionFunction d] (K : CochainComplex 𝒜 ℤ)
    (hResolved :
      ∃ (C₀ : CochainComplex 𝒜 ℤ) (α₀ : K ⟶ C₀), QuasiIso α₀ ∧
        ShiftedDimensionTendsToNegInf d C₀ ∧
        (∀ n : ℤ, ∃ m : ℕ, d (C₀.X n) = m) ∧
        (∃ a : ℤ, ∀ n : ℤ, a ≤ n → d (C₀.X n) = 0)) :
    ∃ (L : CochainComplex 𝒜 ℤ) (α : K ⟶ L), QuasiIso α ∧
      ∀ n : ℤ, d (L.X n) = 0 := by
  rcases hResolved with ⟨C₀, α₀, hα₀, hC₀, hNat₀, hTail₀⟩
  obtain ⟨L, β, hβ, hL⟩ :=
    exists_quasiIso_to_termwise_zero_dimension_of_natValued_and_eventually_zero
      (d := d) C₀ hC₀ hNat₀ hTail₀
  let _ : QuasiIso α₀ := hα₀
  let _ : QuasiIso β := hβ
  -- Proof comment: compose the front-end quasi-isomorphism with the isolated eventual-zero-tail
  -- descent supplied by the previous helper.
  exact ⟨L, α₀ ≫ β, by infer_instance, hL⟩

-- Proof sketch: first use Lemma 13.15.5 to replace the high-degree tail of `K` by a
-- quasi-isomorphic bounded-below complex of `d = 0` objects. Then perform the textbook elementary
-- replacements in finitely many degrees at a time, using the monomorphic envelope axiom and the
-- short-exact-sequence inequality to decrease the quantity `n + d(K.X n)` until every term has
-- dimension zero.
/-- Lemma 13.32.1: if `d` is a cohomological-dimension function on an abelian category and
`n + d(K.X n)` tends to `-∞` as `n → -∞` in the sense that for every integer bound `N` there is a
lower cutoff below which each `d(K.X n)` is finite and satisfies `n + d(K.X n) ≤ N`, then `K` is
quasi-isomorphic to a cochain complex all of whose terms have `d = 0`. -/
@[stacks 07K6]
theorem exists_quasiIso_to_termwise_zero_dimension_of_tendsToNegInf_shifted_dimension
    (d : 𝒜 → WithTop ℕ) [IsCohomologicalDimensionFunction d] (K : CochainComplex 𝒜 ℤ)
    (hK : ShiftedDimensionTendsToNegInf d K) :
    ∃ (L : CochainComplex 𝒜 ℤ) (α : K ⟶ L), QuasiIso α ∧
      ∀ n : ℤ, d (L.X n) = 0 := by
  -- Route correction: the public theorem now reduces to a front-end splice. Once we replace a
  -- far-right truncation by a bounded-below termwise-zero-dimensional resolution and splice it
  -- back into `K`, the isolated eventual-zero-tail `ξ`-descent finishes the proof.
  have hFiniteLeft := eventuallyEqNat_of_shiftedDimensionTendsToNegInf hK 0
  let P : ObjectProperty 𝒜 := fun X ↦ d X = 0
  have hContainsZero : P.ContainsZero := inferInstance
  have hHasMonoEmbedding : P.HasMonoEmbedding := inferInstance
  rcases hFiniteLeft with ⟨a, hLeftNat⟩
  have hLeftNat' : ∀ n : ℤ, n < a → ∃ m : ℕ, d (K.X n) = m := by
    intro n hn
    exact hLeftNat n (le_of_lt hn)
  obtain ⟨I, α, hα⟩ :=
    exists_termwiseMono_quasiIso_with_terms_in_of_isStrictlyGE
      (P := P) a (K.truncGE a) inferInstance
  let β : K ⟶ I := K.πTruncGE a ≫ α
  have hβ : ∀ n : ℤ, a ≤ n → QuasiIsoAt β n := by
    intro n hn
    have hπ : QuasiIsoAt (K.πTruncGE a) n := by
      simpa using CochainComplex.quasiIsoAt_πTruncGE K a n hn
    have hαn : QuasiIsoAt α n := hα.quasiIso.quasiIsoAt n
    let _ : QuasiIsoAt (K.πTruncGE a) n := hπ
    let _ : QuasiIsoAt α n := hαn
    -- Proof comment: the truncation map and the bounded-below replacement are both
    -- quasi-isomorphisms in degrees on and above the cutoff, so their composite is as well.
    infer_instance
  have hRightZero : ∀ n : ℤ, d (I.X n) = 0 := fun n ↦ hα.term_mem n
  -- Proof comment: package the explicit splice as the resolved-zero-tail replacement required by
  -- the general eventual-zero-tail descent helper.
  refine
    exists_quasiIso_to_termwise_zero_dimension_of_resolvedZeroTailReplacement
      (d := d) (K := K) ?_
  refine ⟨resolvedZeroTailSplice (K := K) (I := I) a β,
    resolvedZeroTailSpliceMap (K := K) (I := I) a β, ?_, ?_, ?_, ?_⟩
  · exact resolvedZeroTailSpliceMap_quasiIso (K := K) (I := I) a β hβ
  · exact shiftedDimensionTendsToNegInf_resolvedZeroTailSplice (d := d) a β hK
  · exact resolvedZeroTailSplice_natValued_of_leftNat (d := d) a β hLeftNat' hRightZero
  · exact ⟨a, resolvedZeroTailSplice_zeroTail (d := d) a β hRightZero⟩

end
