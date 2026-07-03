import Serre.Chap14.Infra_14_4_ProjectiveLift
import Serre.Chap14.Corollary_14_14_4_3
import Serre.Chap14.Lemma_14_14_4_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra Representation TensorProduct ZeroObject

universe u w

namespace Representation

section ProjectiveGrothendieckReduction

variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A

-- Proof sketch: the reduction homomorphism is already imported from Corollary `14-14.4-3`; the
-- remaining work here is to combine its class-equality criterion with the projective-lifting
-- statement above.
/-- Helper for Corollary 14-14.4-4: the sum of two projective Grothendieck generator classes is
again represented by an actual finite projective module. -/
private theorem exists_projective_class_sum_rep
    {R : Type u} [CommRing R] [IsLocalRing R]
    {G : Type u} [Group G] [Finite G]
    (P Q : FiniteProjectiveGroupAlgebraModule R G) :
    ∃ W : FiniteProjectiveGroupAlgebraModule R G, [W]ₚ₀ = [P]ₚ₀ + [Q]ₚ₀ := by
  let W0 : ModuleCat R[G] := ModuleCat.of R[G] (P.V × Q.V)
  have hfinite : Module.Finite R[G] W0 := by
    -- Finite generation is preserved by the binary product module.
    change Module.Finite R[G] (P.V × Q.V)
    infer_instance
  let Wfg : FGModuleCat R[G] := ⟨W0, hfinite⟩
  have hproj : Module.Projective R[G] Wfg := by
    -- Projectivity is inherited by binary products.
    change Module.Projective R[G] (P.V × Q.V)
    infer_instance
  let W : FiniteProjectiveGroupAlgebraModule R G := ⟨Wfg, hproj⟩
  let f : P ⟶ W :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.inl R[G] P.V Q.V))
  let g : W ⟶ Q :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.snd R[G] P.V Q.V))
  let r : W ⟶ P :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.fst R[G] P.V Q.V))
  let s : Q ⟶ W :=
    ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.inr R[G] P.V Q.V))
  let T : ShortComplex (FiniteProjectiveGroupAlgebraModule R G) :=
    ShortComplex.mk f g (by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      change (LinearMap.snd R[G] P.V Q.V) ((LinearMap.inl R[G] P.V Q.V) x) = 0
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
      change (LinearMap.fst R[G] P.V Q.V) ((LinearMap.inl R[G] P.V Q.V) x) = x
      simp
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      ext x
      change (LinearMap.snd R[G] P.V Q.V) ((LinearMap.inr R[G] P.V Q.V) x) = x
      simp
    · apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨x, y⟩
      change
        (LinearMap.inl R[G] P.V Q.V ((LinearMap.fst R[G] P.V Q.V) (x, y)) +
            LinearMap.inr R[G] P.V Q.V ((LinearMap.snd R[G] P.V Q.V) (x, y))) =
          (x, y)
      simp
  -- Translate the split short exact sequence into the Grothendieck relation.
  refine ⟨W, ?_⟩
  simpa [T, W, Wfg, W0] using
    finiteProjectiveGroupAlgebraGrothendieckClass_middle_eq_left_add_right
      (A := R) (G := G) T hsplit.shortExact

/-- Helper for Corollary 14-14.4-4: every class in `P₀[R](G)` is a difference of two actual
projective generator classes. -/
private theorem exists_projective_class_difference_rep
    {R : Type u} [CommRing R] [IsLocalRing R]
    {G : Type u} [Group G] [Finite G]
    (x : P₀[R](G)) :
    ∃ P Q : FiniteProjectiveGroupAlgebraModule R G, x = [P]ₚ₀ - [Q]ₚ₀ := by
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · -- The zero class is represented by the zero projective module minus itself.
    refine
      ⟨(0 : FiniteProjectiveGroupAlgebraModule R G),
        (0 : FiniteProjectiveGroupAlgebraModule R G), ?_⟩
    simp
  · intro P
    -- A generator class is already a difference with zero.
    refine ⟨P, (0 : FiniteProjectiveGroupAlgebraModule R G), ?_⟩
    change [P]ₚ₀ = [P]ₚ₀ - [0]ₚ₀
    rw [finiteProjectiveGroupAlgebraGrothendieckClass_zero (A := R) (G := G)]
    exact (sub_zero [P]ₚ₀).symm
  · intro a ha
    rcases ha with ⟨P, Q, hPQ⟩
    -- Negation swaps the two witnesses.
    refine ⟨Q, P, ?_⟩
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using congrArg Neg.neg hPQ
  · intro a b ha hb
    rcases ha with ⟨P, Q, hPQ⟩
    rcases hb with ⟨P', Q', hP'Q'⟩
    obtain ⟨W, hW⟩ :=
      exists_projective_class_sum_rep (R := R) (G := G) P P'
    obtain ⟨Z, hZ⟩ :=
      exists_projective_class_sum_rep (R := R) (G := G) Q Q'
    -- Add the two difference presentations and compress the positive parts again.
    refine ⟨W, Z, ?_⟩
    calc
      QuotientAddGroup.mk' (finiteProjectiveGroupAlgebraGrothendieckRelations R G) (a + b)
          =
            QuotientAddGroup.mk' (finiteProjectiveGroupAlgebraGrothendieckRelations R G) a +
              QuotientAddGroup.mk' (finiteProjectiveGroupAlgebraGrothendieckRelations R G) b := by
              rfl
      _ = ([P]ₚ₀ - [Q]ₚ₀) + ([P']ₚ₀ - [Q']ₚ₀) := by
            simp [hPQ, hP'Q']
      _ = [W]ₚ₀ - [Z]ₚ₀ := by
            simp [hW, hZ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Corollary 14-14.4-4: reduction is injective on projective Grothendieck groups. -/
private theorem projectiveGrothendieckReductionHom_injective :
    Function.Injective (projectiveGrothendieckReductionHom (A := A) (G := G)) := by
  let red : P₀[A](G) →+ P₀[k](G) :=
    projectiveGrothendieckReductionHom (A := A) (G := G)
  intro x y hxy
  obtain ⟨P, Q, hx⟩ := exists_projective_class_difference_rep (R := A) (G := G) x
  obtain ⟨P', Q', hy⟩ := exists_projective_class_difference_rep (R := A) (G := G) y
  obtain ⟨W, hW⟩ := exists_projective_class_sum_rep (R := A) (G := G) P Q'
  obtain ⟨W', hW'⟩ := exists_projective_class_sum_rep (R := A) (G := G) P' Q
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
      Nonempty ((k ⊗[A] W.V) ≃ₗ[k[G]] (k ⊗[A] W'.V)) := by
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

/-- Helper for Corollary 14-14.4-4: a projective generator over the residue field should come from
an actual projective generator upstairs. -/
private theorem exists_reduction_preimage_of_projective_class
    (F : FiniteProjectiveGroupAlgebraModule k G) :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G,
      projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ = [F]ₚ₀ := by
  -- Serre's Proposition 42(b) supplies the projective lift under the Henselian local hypothesis;
  -- the imported owner already converts the lifted reduction isomorphism to Grothendieck classes.
  exact projectiveGrothendieckReductionHom_lifted_projectiveClass_eq (A := A) (G := G) F

/-- Corollary 14-14.4-4: the canonical reduction mod `𝔪` induces a bijection from `P₀[A](G)` onto
`P₀[k](G)`. -/
theorem projectiveGrothendieckReductionHom_bijective :
    Function.Bijective (projectiveGrothendieckReductionHom (A := A) (G := G)) := by
  -- Route correction: reuse the imported reduction homomorphism from Corollary `14-14.4-3`
  -- instead of redeclaring it locally.
  let red : P₀[A](G) →+ P₀[k](G) :=
    projectiveGrothendieckReductionHom (A := A) (G := G)
  refine ⟨projectiveGrothendieckReductionHom_injective (A := A) (G := G), ?_⟩
  intro y
  obtain ⟨P, Q, hy⟩ := exists_projective_class_difference_rep (R := k) (G := G) y
  obtain ⟨P0, hP0⟩ := exists_reduction_preimage_of_projective_class (A := A) (G := G) P
  obtain ⟨Q0, hQ0⟩ := exists_reduction_preimage_of_projective_class (A := A) (G := G) Q
  -- Reduce an arbitrary target class to two lifted generator classes.
  refine ⟨[P0]ₚ₀ - [Q0]ₚ₀, ?_⟩
  calc
    red ([P0]ₚ₀ - [Q0]ₚ₀) = red [P0]ₚ₀ - red [Q0]ₚ₀ := by rw [map_sub]
    _ = [P]ₚ₀ - [Q]ₚ₀ := by rw [hP0, hQ0]
    _ = y := hy.symm

/-- Corollary 14-14.4-4 in derived bridge form: reduction mod `𝔪` identifies `P₀[A](G)` and
`P₀[k](G)` as additive groups. -/
def projectiveGrothendieckReductionEquiv :
    P₀[A](G) ≃+ P₀[k](G) :=
  AddEquiv.ofBijective
    (projectiveGrothendieckReductionHom (A := A) (G := G))
    (projectiveGrothendieckReductionHom_bijective (A := A) (G := G))

end ProjectiveGrothendieckReduction

end Representation
