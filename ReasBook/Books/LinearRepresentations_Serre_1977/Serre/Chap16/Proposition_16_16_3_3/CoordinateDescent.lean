import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_3_3.PositiveBasics

noncomputable section

universe u

open CategoryTheory
open scoped Representation MonoidAlgebra

namespace Representation

section

variable {G : Type u} [Group G]
variable [Finite G]

/-- Helper for Proposition 16-16.3-3: choose one representative from each isomorphism class of
simple finite-dimensional representations over an arbitrary field. -/
theorem existsCompletePairwiseNonisomorphicSimpleFamilyField
    (L : Type u) [Field L] (G : Type u) [Group G] [Finite G] :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep L G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep L G // Simple τ }
  let r : Setoid SimpleRep :=
    { r := fun a b ↦ Nonempty (a.1 ≅ b.1)
      iseqv :=
        { refl := fun a ↦ ⟨Iso.refl _⟩
          symm := by
            intro a b hab
            rcases hab with ⟨iso⟩
            exact ⟨iso.symm⟩
          trans := by
            intro a b c hab hbc
            rcases hab with ⟨eab⟩
            rcases hbc with ⟨ebc⟩
            exact ⟨eab.trans ebc⟩ } }
  let ι : Type (u + 1) := Quotient r
  let π : ι → FDRep L G := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : PairwiseNonisomorphic π := by
    -- Isomorphic chosen representatives determine the same quotient class.
    intro q q' hqq' hIso
    rcases hIso with ⟨iso⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨iso⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine ⟨?_, ?_⟩
    · intro q
      exact (Quotient.out q).2
    · intro τ hτ
      let q : ι := ⟦⟨τ, hτ⟩⟧
      refine ⟨q, ?_⟩
      have hq : Nonempty ((Quotient.out q).1 ≅ τ) :=
        Quotient.exact (Quotient.out_eq q)
      rcases hq with ⟨iso⟩
      exact ⟨iso.symm⟩
  exact ⟨ι, π, hπ_pairwise, hπ_complete⟩

omit [Finite G] in
/-- Helper for Proposition 16-16.3-3: the source of a projective envelope of a simple module is
finitely generated, because essentiality makes any nonzero lift of a simple generator cyclic. -/
theorem moduleFinite_of_projectiveEnvelope_simple
    {L : Type u} [Field L]
    {P M : Type u} [AddCommGroup P] [Module (MonoidAlgebra L G) P]
    [AddCommGroup M] [Module (MonoidAlgebra L G) M]
    [IsSimpleModule (MonoidAlgebra L G) M]
    {f : P →ₗ[MonoidAlgebra L G] M} (hf : f.IsProjectiveEnvelope) :
    Module.Finite (MonoidAlgebra L G) P := by
  letI : Nontrivial M := IsSimpleModule.nontrivial (R := MonoidAlgebra L G) (M := M)
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨x, hx⟩ := hf.surjective m
  let N : Submodule (MonoidAlgebra L G) P := Submodule.span (MonoidAlgebra L G) {x}
  have hmap_ne_bot : N.map f ≠ ⊥ := by
    intro hbot
    have hxmem : f x ∈ N.map f :=
      ⟨x, Submodule.mem_span_singleton_self x, rfl⟩
    have hfx : f x = 0 := by
      rw [hbot] at hxmem
      simpa using hxmem
    exact hm <| by simpa [hx] using hfx
  have hmap_top : N.map f = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top (N.map f)).resolve_left hmap_ne_bot
  have hN_top : N = ⊤ := hf.toIsEssential.eq_top_of_map_eq_top N hmap_top
  -- Once the cyclic span is all of `P`, the singleton generator gives a finite presentation.
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton (MonoidAlgebra L G) P x) := by
    simpa [LinearMap.toSpanSingleton_apply] using
      (Submodule.span_singleton_eq_top_iff (R := MonoidAlgebra L G) (x := x)).1
        (by simpa [N] using hN_top)
  exact Module.Finite.of_surjective
    (LinearMap.toSpanSingleton (MonoidAlgebra L G) P x) hsurj

/-- Helper for Proposition 16-16.3-3: every simple finite-dimensional representation over a field
has a finite projective envelope in the group algebra module category. -/
theorem existsFiniteProjectiveEnvelopeOfSimple
    {L : Type u} [Field L] (τ : FDRep L G) [Simple τ] :
    ∃ P : FiniteProjectiveGroupAlgebraModule L G,
      ∃ f : P.V →ₗ[MonoidAlgebra L G] asModule τ.ρ, f.IsProjectiveEnvelope := by
  let ρ : Representation L G τ := τ.ρ
  letI : Module (MonoidAlgebra L G) τ := by
    simpa using (inferInstance : Module (MonoidAlgebra L G) ρ.asModule)
  letI : Representation.IsIrreducible ρ := by
    simpa [ρ] using (FDRep.isIrreducible_of_simple τ)
  letI : IsSimpleModule (MonoidAlgebra L G) τ := by
    -- Translate simplicity of the `FDRep` owner into simplicity of its group-algebra module.
    simpa [ρ] using (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  let M : ModuleCat (MonoidAlgebra L G) := ModuleCat.of (MonoidAlgebra L G) τ
  let _ : Module.Finite L (MonoidAlgebra L G) := MonoidAlgebra.moduleFinite
  let _ : IsArtinianRing (MonoidAlgebra L G) :=
    IsArtinianRing.of_finite L (MonoidAlgebra L G)
  obtain ⟨P', f', hf'⟩ := exists_isProjectiveEnvelope M
  have hfinite : Module.Finite (MonoidAlgebra L G) P' :=
    moduleFinite_of_projectiveEnvelope_simple
      (G := G) (L := L) (P := P') (M := τ) (f := f'.hom) hf'
  let Pfg : FGModuleCat (MonoidAlgebra L G) := by
    refine ⟨P', ?_⟩
    change Module.Finite (MonoidAlgebra L G) P'
    exact hfinite
  have hproj : Module.Projective (MonoidAlgebra L G) Pfg := by
    -- The Artinian projective envelope already carries projectivity on its source.
    change Module.Projective (MonoidAlgebra L G) P'
    infer_instance
  let P : FiniteProjectiveGroupAlgebraModule L G := ⟨Pfg, hproj⟩
  refine ⟨P, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [ρ] using f'.hom
  -- Repackage the `ModuleCat` envelope as a linear-map envelope on the finite projective source.
  simpa [P, ρ] using hf'

/-- Helper for Proposition 16-16.3-3: a dual family of positive coordinate witnesses converts
positivity in the target basis into positivity of a positive multiple in the source basis, using
only the finite support of the target-basis coordinates. -/
theorem positiveCone_of_nsmulDualCoordinateWitnesses
    {ι : Type u} {κ : Type*}
    {P RK : Type*}
    [AddCommGroup P] [AddCommGroup RK]
    (bP : Module.Basis ι ℤ P)
    (bK : Module.Basis κ ℤ RK)
    (f : P →ₗ[ℤ] RK)
    {n : ℕ}
    (z : ι → RK)
    (hdual :
      ∀ i y,
        bP.repr (n • y) i =
          (bK.repr (f y)).sum fun j a ↦ a * bK.repr (z i) j)
    {y : P}
    (hy : f y ∈ bK.positiveCone)
    (hz : ∀ i, z i ∈ bK.positiveCone) :
    n • y ∈ bP.positiveCone := by
  -- It remains only to read each source coordinate as a nonnegative finite-support dot product.
  intro i
  rw [hdual i y]
  exact Finsupp.sum_nonneg fun j _ ↦ mul_nonneg (hy j) ((hz i) j)

/-- Helper for Proposition 16-16.3-3: a scaled dual family of positive coordinate witnesses
converts target-basis positivity into positivity of the same positive multiple in the source
basis. -/
theorem positiveCone_of_scaledNsmulDualCoordinateWitnesses
    {ι : Type u} {κ : Type*}
    {P RK : Type*}
    [AddCommGroup P] [AddCommGroup RK]
    (bP : Module.Basis ι ℤ P)
    (bK : Module.Basis κ ℤ RK)
    (f : P →ₗ[ℤ] RK)
    {n : ℕ}
    (z : ι → RK)
    (hdual :
      ∀ i y,
        bP.repr (n • y) i =
          (n : ℤ) *
            ((bK.repr (f y)).sum fun j a ↦ a * bK.repr (z i) j))
    {y : P}
    (hn : 0 ≤ (n : ℤ))
    (hy : f y ∈ bK.positiveCone)
    (hz : ∀ i, z i ∈ bK.positiveCone) :
    n • y ∈ bP.positiveCone := by
  intro i
  rw [hdual i y]
  exact mul_nonneg hn <| Finsupp.sum_nonneg fun j _ ↦ mul_nonneg (hy j) ((hz i) j)

/-- Helper for Proposition 16-16.3-3: weighted scaled dual witnesses still force positivity after
dividing by the positive source weight. -/
theorem positiveCone_of_weightedScaledDualCoordinateWitnesses
    {ι : Type u} {κ : Type*}
    {P RK : Type*}
    [AddCommGroup P] [AddCommGroup RK]
    (bP : Module.Basis ι ℤ P)
    (bK : Module.Basis κ ℤ RK)
    (f : P →ₗ[ℤ] RK)
    {n : ℕ}
    (wP : ι → ℤ) (wK : κ → ℤ)
    (z : ι → RK)
    (hdual :
      ∀ i y,
        wP i * bP.repr (n • y) i =
          (n : ℤ) *
            ((bK.repr (f y)).sum fun j a ↦
              a * (wK j * bK.repr (z i) j)))
    (hwP_pos : ∀ i, 0 < wP i)
    (hwK_nonneg : ∀ j, 0 ≤ wK j)
    (hn : 0 ≤ (n : ℤ))
    {y : P}
    (hy : f y ∈ bK.positiveCone)
    (hz : ∀ i, z i ∈ bK.positiveCone) :
    n • y ∈ bP.positiveCone := by
  intro i
  -- The weighted coordinate is a product of nonnegative target coordinates and weights.
  have hweighted :
      0 ≤ wP i * bP.repr (n • y) i := by
    rw [hdual i y]
    refine mul_nonneg hn ?_
    exact
      Finsupp.sum_nonneg fun j _ ↦
        mul_nonneg (hy j) (mul_nonneg (hwK_nonneg j) ((hz i) j))
  -- Since the source Schur weight is strictly positive, the underlying coordinate is nonnegative.
  rw [mul_comm] at hweighted
  exact nonneg_of_mul_nonneg_left hweighted (hwP_pos i)

/-- Helper for Proposition 16-16.3-3: weighted coordinate witnesses with nonnegative right-hand
sides force every basis coordinate to be nonnegative. -/
theorem positiveCone_of_weightedScaledCoordinateWitnesses
    {ι P : Type*}
    [AddCommGroup P]
    (b : Module.Basis ι ℤ P)
    {n : ℕ} {w : ι → ℤ} {x : P}
    (hw_pos : ∀ i, 0 < w i)
    (hn : 0 ≤ (n : ℤ))
    (hcoord : ∀ i, ∃ c : ℤ, 0 ≤ c ∧ w i * b.repr x i = (n : ℤ) * c) :
    x ∈ b.positiveCone := by
  intro i
  rcases hcoord i with ⟨c, hc_nonneg, hcoord_i⟩
  -- The witness makes the weighted coordinate nonnegative.
  have hweighted : 0 ≤ w i * b.repr x i := by
    rw [hcoord_i]
    exact mul_nonneg hn hc_nonneg
  -- Divide by the strictly positive Schur weight at the ordered-integer level.
  rw [mul_comm] at hweighted
  exact nonneg_of_mul_nonneg_left hweighted (hw_pos i)

/-- Helper for Proposition 16-16.3-3: the integer dot product of two finitely supported
coordinate families is symmetric. -/
theorem finsupp_intDot_comm {κ : Type*} (f g : κ →₀ ℤ) :
    f.sum (fun j a ↦ a * g j) = g.sum (fun j a ↦ a * f j) := by
  classical
  -- Expand each coefficient as a diagonal double sum, commute the finite sums, then collapse.
  calc
    f.sum (fun j a ↦ a * g j)
        = f.sum (fun j a ↦ g.sum fun l b ↦ if j = l then a * b else 0) := by
            apply Finsupp.sum_congr
            intro j hj
            rw [Finsupp.sum_eq_single j]
            · simp
            · intro l _ hlj
              have hjl : j ≠ l := fun h ↦ hlj h.symm
              simp [hjl]
            · intro _
              simp
    _ = g.sum (fun l b ↦ f.sum fun j a ↦ if j = l then a * b else 0) := by
          rw [Finsupp.sum_comm]
    _ = g.sum (fun l b ↦ b * f l) := by
          apply Finsupp.sum_congr
          intro l _
          rw [Finsupp.sum_eq_single l]
          · simp [mul_comm]
          · intro j _ hjl
            simp [hjl]
          · intro _
            simp

/-- Helper for Proposition 16-16.3-3: a weighted integer dot product is symmetric after moving the
weight to the other finite-support coordinate family. -/
theorem finsupp_weighted_intDot_comm {κ : Type*} (w : κ → ℤ) (f g : κ →₀ ℤ) :
    f.sum (fun j a ↦ a * (w j * g j)) =
      g.sum (fun j a ↦ w j * a * f j) := by
  classical
  -- Expand each coefficient as a diagonal double sum, commute the sums, and collapse again.
  calc
    f.sum (fun j a ↦ a * (w j * g j))
        = f.sum (fun j a ↦ g.sum fun l b ↦ if j = l then a * (w l * b) else 0) := by
            apply Finsupp.sum_congr
            intro j _hj
            rw [Finsupp.sum_eq_single j]
            · simp
            · intro l _ hlj
              have hjl : j ≠ l := fun h ↦ hlj h.symm
              simp [hjl]
            · intro _
              simp
    _ = g.sum (fun l b ↦ f.sum fun j a ↦ if j = l then a * (w l * b) else 0) := by
          rw [Finsupp.sum_comm]
    _ = g.sum (fun l b ↦ w l * b * f l) := by
          apply Finsupp.sum_congr
          intro l _
          rw [Finsupp.sum_eq_single l]
          · simp
            ring
          · intro j _ hjl
            simp [hjl]
          · intro _
            simp

/-- Helper for Proposition 16-16.3-3: dotting the coordinates of `x` with a basis vector reads
off the corresponding coordinate of `x`. -/
theorem basisDotPairing_basis_right
    {ι M : Type*} [AddCommGroup M]
    (b : Module.Basis ι ℤ M) (x : M) (i : ι) :
    (b.repr x).sum (fun j a ↦ a * b.repr (b i) j) = b.repr x i := by
  classical
  -- Replace the right basis vector by its single-coordinate representation and collapse the sum.
  rw [b.repr_self i]
  rw [Finsupp.sum_eq_single i]
  · simp
  · intro j _hj hji
    exact mul_eq_zero_of_right _ (Finsupp.single_eq_of_ne hji)
  · intro hzero
    simp

/-- Helper for Proposition 16-16.3-3: transpose-column identities against a dual family give the
coordinate formula needed by the positive-cone descent lemma. -/
theorem dualCoordinateIdentity_of_transposeColumns
    {ι κ P RK Rk' : Type*}
    [AddCommGroup P] [AddCommGroup RK] [AddCommGroup Rk']
    (bP : Module.Basis ι ℤ P)
    (bK : Module.Basis κ ℤ RK)
    (f : P →ₗ[ℤ] RK)
    (d : RK →ₗ[ℤ] Rk')
    (ψ : ι → Rk' →ₗ[ℤ] ℤ)
    {n : ℕ}
    (z : ι → RK)
    (hentry : ∀ l j, bK.repr (f (bP l)) j = ψ l (d (bK j)))
    (hcolumn : ∀ i l, ψ l (d (z i)) = bP.repr (n • bP i) l) :
    ∀ i y,
      bP.repr (n • y) i =
        (bK.repr (f y)).sum fun j a ↦ a * bK.repr (z i) j := by
  intro i
  let lhs : P →ₗ[ℤ] ℤ :=
    (n : ℤ) • ((Finsupp.lapply i).comp bP.repr.toLinearMap)
  let rhs : P →ₗ[ℤ] ℤ :=
    (bK.constr ℤ fun j ↦ bK.repr (z i) j).comp f
  have hmaps : lhs = rhs := by
    -- Since both sides are linear in `y`, it is enough to compare them on the source basis.
    apply bP.ext
    intro l
    have hdelta : lhs (bP l) = bP.repr (n • bP i) l := by
      by_cases hli : l = i
      · subst l
        simp [lhs]
      · have hil : i ≠ l := fun h ↦ hli h.symm
        simp [lhs, hli, hil]
    calc
      lhs (bP l) = bP.repr (n • bP i) l := hdelta
      _ = ψ l (d (z i)) := (hcolumn i l).symm
      _ = ((bK.constr ℤ fun j ↦ ψ l (d (bK j))) (z i)) := by
            -- The functional `ψ l ∘ d` is determined by its values on the `bK` basis.
            have hmap : (bK.constr ℤ fun j ↦ ψ l (d (bK j))) = (ψ l).comp d := by
              apply bK.ext
              intro j
              simp [Module.Basis.constr_basis]
            simpa using congrArg (fun f : RK →ₗ[ℤ] ℤ ↦ f (z i)) hmap.symm
      _ = ((bK.constr ℤ fun j ↦ bK.repr (f (bP l)) j) (z i)) := by
            -- Replace the dual functional values by the transpose entries.
            have hfun : (fun j ↦ ψ l (d (bK j))) = fun j ↦ bK.repr (f (bP l)) j := by
              funext j
              exact (hentry l j).symm
            rw [hfun]
      _ = (bK.repr (z i)).sum (fun j a ↦ a * bK.repr (f (bP l)) j) := by
            simp [Module.Basis.constr_apply]
      _ = (bK.repr (f (bP l))).sum (fun j a ↦ a * bK.repr (z i) j) := by
            rw [finsupp_intDot_comm]
      _ = rhs (bP l) := by
            simp [rhs, Module.Basis.constr_apply]
  intro y
  -- Evaluate the equality of linear maps and unfold the two coordinate functionals.
  have hy := congrArg (fun f : P →ₗ[ℤ] ℤ ↦ f y) hmaps
  simpa [lhs, rhs, Module.Basis.constr_apply] using hy

/-- Helper for Proposition 16-16.3-3: a residue-degree-scaled transpose identity gives the
coordinate formula needed by the positive-cone descent lemma. -/
theorem scaledDualCoordinateIdentity_of_transposeColumns
    {ι κ P RK Rk' : Type*}
    [AddCommGroup P] [AddCommGroup RK] [AddCommGroup Rk']
    (bP : Module.Basis ι ℤ P)
    (bK : Module.Basis κ ℤ RK)
    (f : P →ₗ[ℤ] RK)
    (d : RK →ₗ[ℤ] Rk')
    (ψ : ι → Rk' →ₗ[ℤ] ℤ)
    {n : ℕ}
    (z : ι → RK)
    (hentry : ∀ l j, ψ l (d (bK j)) = (n : ℤ) * bK.repr (f (bP l)) j)
    (hcolumn : ∀ i l, ψ l (d (z i)) = bP.repr (n • bP i) l) :
    ∀ i y,
      bP.repr (n • y) i =
        (n : ℤ) *
          ((bK.repr (f y)).sum fun j a ↦ a * bK.repr (z i) j) := by
  intro i
  let lhs : P →ₗ[ℤ] ℤ :=
    (n : ℤ) • ((Finsupp.lapply i).comp bP.repr.toLinearMap)
  let rhs : P →ₗ[ℤ] ℤ :=
    (n : ℤ) • ((bK.constr ℤ fun j ↦ bK.repr (z i) j).comp f)
  have hmaps : lhs = rhs := by
    apply bP.ext
    intro l
    have hdelta : lhs (bP l) = bP.repr (n • bP i) l := by
      by_cases hli : l = i
      · subst l
        simp [lhs]
      · have hil : i ≠ l := fun h ↦ hli h.symm
        simp [lhs, hli, hil]
    calc
      lhs (bP l) = bP.repr (n • bP i) l := hdelta
      _ = ψ l (d (z i)) := (hcolumn i l).symm
      _ = ((bK.constr ℤ fun j ↦ ψ l (d (bK j))) (z i)) := by
            have hmap : (bK.constr ℤ fun j ↦ ψ l (d (bK j))) = (ψ l).comp d := by
              apply bK.ext
              intro j
              simp [Module.Basis.constr_basis]
            simpa using congrArg (fun f : RK →ₗ[ℤ] ℤ ↦ f (z i)) hmap.symm
      _ = ((bK.constr ℤ fun j ↦ (n : ℤ) * bK.repr (f (bP l)) j) (z i)) := by
            have hfun :
                (fun j ↦ ψ l (d (bK j))) =
                  fun j ↦ (n : ℤ) * bK.repr (f (bP l)) j := by
              funext j
              exact hentry l j
            rw [hfun]
      _ = (bK.repr (z i)).sum
            (fun j a ↦ a * ((n : ℤ) * bK.repr (f (bP l)) j)) := by
            simp [Module.Basis.constr_apply]
      _ = (n : ℤ) *
            ((bK.repr (z i)).sum (fun j a ↦ a * bK.repr (f (bP l)) j)) := by
            simp [Finsupp.sum, Finset.mul_sum, mul_left_comm]
      _ = (n : ℤ) *
            ((bK.repr (f (bP l))).sum (fun j a ↦ a * bK.repr (z i) j)) := by
            rw [finsupp_intDot_comm]
      _ = rhs (bP l) := by
            simp [rhs, Module.Basis.constr_apply]
  intro y
  have hy := congrArg (fun f : P →ₗ[ℤ] ℤ ↦ f y) hmaps
  simpa [lhs, rhs, Module.Basis.constr_apply] using hy

/-- Helper for Proposition 16-16.3-3: transpose-column identities and positive column witnesses
give positivity of a positive multiple in the source basis. -/
theorem positiveCone_of_transposeColumns
    {ι κ P RK Rk' : Type*}
    [AddCommGroup P] [AddCommGroup RK] [AddCommGroup Rk']
    (bP : Module.Basis ι ℤ P)
    (bK : Module.Basis κ ℤ RK)
    (f : P →ₗ[ℤ] RK)
    (d : RK →ₗ[ℤ] Rk')
    (ψ : ι → Rk' →ₗ[ℤ] ℤ)
    {n : ℕ}
    (z : ι → RK)
    (hentry : ∀ l j, bK.repr (f (bP l)) j = ψ l (d (bK j)))
    (hcolumn : ∀ i l, ψ l (d (z i)) = bP.repr (n • bP i) l)
    {y : P}
    (hy : f y ∈ bK.positiveCone)
    (hz : ∀ i, z i ∈ bK.positiveCone) :
    n • y ∈ bP.positiveCone := by
  -- First convert the transpose identities into a coordinate formula for `n • y`.
  have hdual :
      ∀ i y,
        bP.repr (n • y) i =
          (bK.repr (f y)).sum fun j a ↦ a * bK.repr (z i) j :=
    dualCoordinateIdentity_of_transposeColumns
      bP bK f d ψ z hentry hcolumn
  -- The coordinate formula is a finite dot product of nonnegative coordinates.
  exact positiveCone_of_nsmulDualCoordinateWitnesses bP bK f z hdual hy hz

/-- Helper for Proposition 16-16.3-3: scaled transpose-column identities and positive column
witnesses give positivity of a positive multiple in the source basis. -/
theorem positiveCone_of_scaledTransposeColumns
    {ι κ P RK Rk' : Type*}
    [AddCommGroup P] [AddCommGroup RK] [AddCommGroup Rk']
    (bP : Module.Basis ι ℤ P)
    (bK : Module.Basis κ ℤ RK)
    (f : P →ₗ[ℤ] RK)
    (d : RK →ₗ[ℤ] Rk')
    (ψ : ι → Rk' →ₗ[ℤ] ℤ)
    {n : ℕ}
    (z : ι → RK)
    (hentry : ∀ l j, ψ l (d (bK j)) = (n : ℤ) * bK.repr (f (bP l)) j)
    (hcolumn : ∀ i l, ψ l (d (z i)) = bP.repr (n • bP i) l)
    {y : P}
    (hn : 0 ≤ (n : ℤ))
    (hy : f y ∈ bK.positiveCone)
    (hz : ∀ i, z i ∈ bK.positiveCone) :
    n • y ∈ bP.positiveCone := by
  have hdual :
      ∀ i y,
        bP.repr (n • y) i =
          (n : ℤ) *
            ((bK.repr (f y)).sum fun j a ↦ a * bK.repr (z i) j) :=
    scaledDualCoordinateIdentity_of_transposeColumns
      bP bK f d ψ z hentry hcolumn
  exact positiveCone_of_scaledNsmulDualCoordinateWitnesses bP bK f z hdual hn hy hz

/-- Helper for Proposition 16-16.3-3: a scaled adjunction identity against all target classes gives
the direct dual-coordinate formula used in the source positivity proof. -/
theorem scaledDualCoordinateIdentity_of_brauerAdjunction
    {ι κ P RK Rk' : Type*}
    [AddCommGroup P] [AddCommGroup RK] [AddCommGroup Rk']
    (bP : Module.Basis ι ℤ P)
    (bK : Module.Basis κ ℤ RK)
    (f : P →ₗ[ℤ] RK)
    (d : RK →ₗ[ℤ] Rk')
    (ψ : ι → Rk' →ₗ[ℤ] ℤ)
    {n : ℕ}
    (z : ι → RK)
    (hadj :
      ∀ l x,
        ψ l (d x) =
          (n : ℤ) *
            ((bK.repr (f (bP l))).sum fun j a ↦ a * bK.repr x j))
    (hcolumn : ∀ i l, ψ l (d (z i)) = bP.repr (n • bP i) l) :
    ∀ i y,
      bP.repr (n • y) i =
        (n : ℤ) *
          ((bK.repr (f y)).sum fun j a ↦ a * bK.repr (z i) j) := by
  intro i
  let lhs : P →ₗ[ℤ] ℤ :=
    (n : ℤ) • ((Finsupp.lapply i).comp bP.repr.toLinearMap)
  let rhs : P →ₗ[ℤ] ℤ :=
    (n : ℤ) • ((bK.constr ℤ fun j ↦ bK.repr (z i) j).comp f)
  have hmaps : lhs = rhs := by
    -- It is enough to compare the two coefficient functionals on the projective basis.
    apply bP.ext
    intro l
    have hdelta : lhs (bP l) = bP.repr (n • bP i) l := by
      by_cases hli : l = i
      · subst l
        simp [lhs]
      · have hil : i ≠ l := fun h ↦ hli h.symm
        simp [lhs, hli, hil]
    calc
      lhs (bP l) = bP.repr (n • bP i) l := hdelta
      _ = ψ l (d (z i)) := (hcolumn i l).symm
      _ = (n : ℤ) *
            ((bK.repr (f (bP l))).sum fun j a ↦ a * bK.repr (z i) j) := by
            exact hadj l (z i)
      _ = rhs (bP l) := by
            simp [rhs, Module.Basis.constr_apply]
  intro y
  -- Evaluate the equality of linear maps and unfold both coefficient functionals.
  have hy := congrArg (fun g : P →ₗ[ℤ] ℤ ↦ g y) hmaps
  simpa [lhs, rhs, Module.Basis.constr_apply] using hy

/-- Helper for Proposition 16-16.3-3: a Schur-weighted adjunction against all target classes gives
the weighted dual-coordinate formula used by the weighted positivity descent lemma. -/
theorem weightedDualCoordinateIdentity_of_brauerAdjunction
    {ι κ P RK Rk' : Type*}
    [AddCommGroup P] [AddCommGroup RK] [AddCommGroup Rk']
    (bP : Module.Basis ι ℤ P)
    (bK : Module.Basis κ ℤ RK)
    (f : P →ₗ[ℤ] RK)
    (d : RK →ₗ[ℤ] Rk')
    (ψ : ι → Rk' →ₗ[ℤ] ℤ)
    {n : ℕ}
    (wP : ι → ℤ) (wK : κ → ℤ)
    (z : ι → RK)
    (hadj :
      ∀ l x,
        wP l * ψ l (d x) =
          (n : ℤ) *
            ((bK.repr (f (bP l))).sum fun j a ↦
              wK j * a * bK.repr x j))
    (hcolumn : ∀ i l, ψ l (d (z i)) = bP.repr (n • bP i) l) :
    ∀ i y,
      wP i * bP.repr (n • y) i =
        (n : ℤ) *
          ((bK.repr (f y)).sum fun j a ↦
            a * (wK j * bK.repr (z i) j)) := by
  intro i
  let lhs : P →ₗ[ℤ] ℤ :=
    (wP i) • ((n : ℤ) • ((Finsupp.lapply i).comp bP.repr.toLinearMap))
  let rhs : P →ₗ[ℤ] ℤ :=
    (n : ℤ) • ((bK.constr ℤ fun j ↦ wK j * bK.repr (z i) j).comp f)
  have hmaps : lhs = rhs := by
    -- Compare the two weighted coefficient functionals on the projective basis.
    apply bP.ext
    intro l
    have hleftColumn : lhs (bP l) = wP l * ψ l (d (z i)) := by
      by_cases hli : l = i
      · subst l
        calc
          lhs (bP i) = wP i * bP.repr (n • bP i) i := by
            simp [lhs]
          _ = wP i * ψ i (d (z i)) := by
            rw [hcolumn i i]
      · have hil : i ≠ l := fun h ↦ hli h.symm
        have hψ : ψ l (d (z i)) = 0 := by
          rw [hcolumn i l]
          simp [hli]
        calc
          lhs (bP l) = 0 := by
            simp [lhs, hil]
          _ = wP l * ψ l (d (z i)) := by
            rw [hψ, mul_zero]
    calc
      lhs (bP l) = wP l * ψ l (d (z i)) := hleftColumn
      _ =
          (n : ℤ) *
            ((bK.repr (f (bP l))).sum fun j a ↦
              a * (wK j * bK.repr (z i) j)) := by
            rw [hadj l (z i)]
            congr 1
            apply Finsupp.sum_congr
            intro j _hj
            ring
      _ = rhs (bP l) := by
            simp [rhs, Module.Basis.constr_apply]
  intro y
  -- Evaluate the equality of weighted coefficient functionals on the arbitrary source class.
  have hy := congrArg (fun g : P →ₗ[ℤ] ℤ ↦ g y) hmaps
  simpa [lhs, rhs, Module.Basis.constr_apply] using hy

end

end Representation
