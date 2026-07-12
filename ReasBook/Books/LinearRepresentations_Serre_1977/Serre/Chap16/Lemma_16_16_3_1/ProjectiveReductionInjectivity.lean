import LinearRepresentations_Serre_1977.Chap16.Lemma_16_16_3_1.PositiveConeBridge

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra Representation TensorProduct ZeroObject

namespace Representation

section ProjectivePositiveSubset

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Lemma 16-16.3-1: reduction of an actual projective class is still actual over the
residue field. -/
private theorem reduction_mem_projectivePositiveSubset_of_mem
    {x : P₀[A](G)} (hx : x ∈ P⁺[A](G)) :
    projectiveGrothendieckReductionHom (A := A) (G := G) x ∈ P⁺[k](G) := by
  rcases (mem_projectivePositiveSubset_iff A G).1 hx with ⟨P, hP⟩
  -- Reduce the actual witness and rewrite its class through the reduction homomorphism.
  refine (mem_projectivePositiveSubset_iff k G).2 ?_
  refine ⟨P.residueFieldReduction, ?_⟩
  calc
    [P.residueFieldReduction]ₚ₀
        = (projectiveGrothendieckReductionHom (A := A) (G := G)) [P]ₚ₀ := by
            symm
            exact projectiveGrothendieckReductionHom_projectiveClass_eq (A := A) (G := G) P
    _ = (projectiveGrothendieckReductionHom (A := A) (G := G)) x := by rw [hP]

theorem reduction_nsmul_mem_projectivePositiveSubset
    {x : P₀[A](G)} {n : ℕ} (hx : n • x ∈ P⁺[A](G)) :
    n • (projectiveGrothendieckReductionHom (A := A) (G := G)) x ∈ P⁺[k](G) := by
  -- First reduce the actual witness for `n • x`, then pull the scalar through the additive map.
  have hxred :
      (projectiveGrothendieckReductionHom (A := A) (G := G)) (n • x) ∈ P⁺[k](G) :=
    reduction_mem_projectivePositiveSubset_of_mem (A := A) (G := G) hx
  simpa using hxred

/-- Helper for Lemma 16-16.3-1: the sum of two actual projective classes is again represented by
an actual finite projective module. -/
private theorem exists_projective_class_sum_rep_local
    (P Q : FiniteProjectiveGroupAlgebraModule A G) :
    ∃ W : FiniteProjectiveGroupAlgebraModule A G, [W]ₚ₀ = [P]ₚ₀ + [Q]ₚ₀ := by
  let W0 : ModuleCat A[G] := ModuleCat.of A[G] (P.V × Q.V)
  have hfinite : Module.Finite A[G] W0 := by
    -- Finite generation is preserved by the binary product module.
    change Module.Finite A[G] (P.V × Q.V)
    infer_instance
  let Wfg : FGModuleCat A[G] := ⟨W0, hfinite⟩
  have hproj : Module.Projective A[G] Wfg := by
    -- Projectivity is inherited by binary products.
    change Module.Projective A[G] (P.V × Q.V)
    infer_instance
  let W : FiniteProjectiveGroupAlgebraModule A G := ⟨Wfg, hproj⟩
  let f : P ⟶ W :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.inl A[G] P.V Q.V))
  let g : W ⟶ Q :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.snd A[G] P.V Q.V))
  let r : W ⟶ P :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.fst A[G] P.V Q.V))
  let s : Q ⟶ W :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.inr A[G] P.V Q.V))
  let T : ShortComplex (FiniteProjectiveGroupAlgebraModule A G) :=
    ShortComplex.mk f g (by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      change (LinearMap.snd A[G] P.V Q.V) ((LinearMap.inl A[G] P.V Q.V) x) = 0
      simp)
  have hsplit : T.Splitting := by
    -- The standard inclusions and projections split the product short complex.
    refine
      { r := r
        s := s
        f_r := ?_
        s_g := ?_
        id := ?_ }
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      change (LinearMap.fst A[G] P.V Q.V) ((LinearMap.inl A[G] P.V Q.V) x) = x
      simp
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      change (LinearMap.snd A[G] P.V Q.V) ((LinearMap.inr A[G] P.V Q.V) x) = x
      simp
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨x, y⟩
      change
        (LinearMap.inl A[G] P.V Q.V ((LinearMap.fst A[G] P.V Q.V) (x, y)) +
            LinearMap.inr A[G] P.V Q.V ((LinearMap.snd A[G] P.V Q.V) (x, y))) =
          (x, y)
      simp
  -- Translate the split short exact sequence into the Grothendieck relation.
  refine ⟨W, ?_⟩
  simpa [T, W, Wfg, W0] using
    finiteProjectiveGroupAlgebraGrothendieckClass_middle_eq_left_add_right
      (A := A) (G := G) T ⟨LinearEquiv.refl A[G] (P.V × Q.V)⟩

/-- Helper for Lemma 16-16.3-1: every class in `P_A(G)` is a difference of two actual projective
generator classes. -/
private theorem exists_projective_class_difference_rep_local
    (x : P₀[A](G)) :
    ∃ P Q : FiniteProjectiveGroupAlgebraModule A G, x = [P]ₚ₀ - [Q]ₚ₀ := by
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · -- The zero class is represented by the zero projective module minus itself.
    refine
      ⟨(0 : FiniteProjectiveGroupAlgebraModule A G),
        (0 : FiniteProjectiveGroupAlgebraModule A G), ?_⟩
    simp
  · intro P
    -- A generator class is already a difference with zero.
    refine ⟨P, (0 : FiniteProjectiveGroupAlgebraModule A G), ?_⟩
    change [P]ₚ₀ = [P]ₚ₀ - [0]ₚ₀
    rw [finiteProjectiveGroupAlgebraGrothendieckClass_zero (A := A) (G := G)]
    exact (sub_zero [P]ₚ₀).symm
  · intro a ha
    rcases ha with ⟨P, Q, hPQ⟩
    -- Negation swaps the two witnesses.
    refine ⟨Q, P, ?_⟩
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using congrArg Neg.neg hPQ
  · intro a b ha hb
    rcases ha with ⟨P, Q, hPQ⟩
    rcases hb with ⟨P', Q', hP'Q'⟩
    obtain ⟨W, hW⟩ := exists_projective_class_sum_rep_local (A := A) (G := G) P P'
    obtain ⟨Z, hZ⟩ := exists_projective_class_sum_rep_local (A := A) (G := G) Q Q'
    -- Add the two difference presentations and compress the positive parts again.
    refine ⟨W, Z, ?_⟩
    calc
      QuotientAddGroup.mk' (finiteProjectiveGroupAlgebraGrothendieckRelations A G) (a + b)
          =
            QuotientAddGroup.mk' (finiteProjectiveGroupAlgebraGrothendieckRelations A G) a +
              QuotientAddGroup.mk' (finiteProjectiveGroupAlgebraGrothendieckRelations A G) b := by
              rfl
      _ = ([P]ₚ₀ - [Q]ₚ₀) + ([P']ₚ₀ - [Q']ₚ₀) := by
            simp [hPQ, hP'Q']
      _ = [W]ₚ₀ - [Z]ₚ₀ := by
            simp [hW, hZ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 16-16.3-1: reduction is injective on projective Grothendieck groups even
before the missing positive-lift step is supplied. -/
theorem projectiveGrothendieckReductionHom_injective_local :
    Function.Injective (projectiveGrothendieckReductionHom (A := A) (G := G)) := by
  let red : P₀[A](G) →+ P₀[k](G) :=
    projectiveGrothendieckReductionHom (A := A) (G := G)
  intro x y hxy
  obtain ⟨P, Q, hx⟩ := exists_projective_class_difference_rep_local (A := A) (G := G) x
  obtain ⟨P', Q', hy⟩ := exists_projective_class_difference_rep_local (A := A) (G := G) y
  obtain ⟨W, hW⟩ := exists_projective_class_sum_rep_local (A := A) (G := G) P Q'
  obtain ⟨W', hW'⟩ := exists_projective_class_sum_rep_local (A := A) (G := G) P' Q
  have hdiff :
      red ([P]ₚ₀ - [Q]ₚ₀) = red ([P']ₚ₀ - [Q']ₚ₀) := by
    simpa [red, hx, hy] using hxy
  have hdiff' :
      [P.residueFieldReduction]ₚ₀ - [Q.residueFieldReduction]ₚ₀ =
        [P'.residueFieldReduction]ₚ₀ - [Q'.residueFieldReduction]ₚ₀ := by
    simpa [map_sub, red] using hdiff
  have hsumred :
      [P.residueFieldReduction]ₚ₀ + [Q'.residueFieldReduction]ₚ₀ =
        [P'.residueFieldReduction]ₚ₀ + [Q.residueFieldReduction]ₚ₀ := by
    -- Move the equality of differences to an equality of sums in the residue-field group.
    exact sub_eq_sub_iff_add_eq_add.mp hdiff'
  have hWred :
      [W.residueFieldReduction]ₚ₀ = [W'.residueFieldReduction]ₚ₀ := by
    -- Rewrite both sides through the reduction map and the two sum witnesses.
    calc
      [W.residueFieldReduction]ₚ₀ = red [W]ₚ₀ := by
        symm
        simpa [red] using projectiveGrothendieckReductionHom_projectiveClass_eq
          (A := A) (G := G) W
      _ = red ([P]ₚ₀ + [Q']ₚ₀) := by rw [hW]
      _ = red [P]ₚ₀ + red [Q']ₚ₀ := by rw [map_add]
      _ = [P.residueFieldReduction]ₚ₀ + [Q'.residueFieldReduction]ₚ₀ := by
            simp [red]
      _ = [P'.residueFieldReduction]ₚ₀ + [Q.residueFieldReduction]ₚ₀ := hsumred
      _ = red [P']ₚ₀ + red [Q]ₚ₀ := by simp [red]
      _ = red ([P']ₚ₀ + [Q]ₚ₀) := by rw [map_add]
      _ = red [W']ₚ₀ := by rw [hW']
      _ = [W'.residueFieldReduction]ₚ₀ := by
            simpa [red] using projectiveGrothendieckReductionHom_projectiveClass_eq
              (A := A) (G := G) W'
  have hred_lin' :
      Nonempty
        (W.residueFieldReduction.V ≃ₗ[k[G]] W'.residueFieldReduction.V) := by
    -- Equality of projective classes over the field is already classified by linear equivalence.
    exact
      (finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_linearEquiv
        (A := k) (G := G) W.residueFieldReduction W'.residueFieldReduction).1 hWred
  have hred_lin :
      Nonempty
        (((IsLocalRing.ResidueField A) ⊗[A] W.V) ≃ₗ[(IsLocalRing.ResidueField A)[G]]
          ((IsLocalRing.ResidueField A) ⊗[A] W'.V)) := by
    -- Unfold the intrinsic reduction owner back to the tensor-product reduction module.
    simpa [FiniteProjectiveGroupAlgebraModule.residueFieldReduction,
      FiniteProjectiveGroupAlgebraModule.V] using hred_lin'
  have hlin :
      Nonempty (W.V ≃ₗ[A[G]] W'.V) := by
    -- Lemma `14-14.4-2` lifts the reduced equivalence back to the local coefficient ring.
    exact
      (projective_monoidAlgebra_nonempty_linearEquiv_iff_reduction_nonempty_linearEquiv
        (Λ := A) (G := G) (P := W.V) (P' := W'.V)
        (by infer_instance) (by infer_instance)).2 hred_lin
  have hsum :
      [P]ₚ₀ + [Q']ₚ₀ = [P']ₚ₀ + [Q]ₚ₀ := by
    -- Convert the lifted linear equivalence back to equality of Grothendieck classes upstairs.
    calc
      [P]ₚ₀ + [Q']ₚ₀ = [W]ₚ₀ := hW.symm
      _ = [W']ₚ₀ :=
        (finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_linearEquiv
          (A := A) (G := G) W W').2 hlin
      _ = [P']ₚ₀ + [Q]ₚ₀ := hW'
  have hclass :
      [P]ₚ₀ - [Q]ₚ₀ = [P']ₚ₀ - [Q']ₚ₀ := by
    -- Cancel the common summands from the equality of sums.
    exact sub_eq_sub_iff_add_eq_add.mpr hsum
  exact hx.trans (hclass.trans hy.symm)

end ProjectivePositiveSubset

end Representation
