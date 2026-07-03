import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Remark_2_2_4_4
import LinearRepresentations_Serre_1977.Chap06.Proposition_6_6_3_1
import LinearRepresentations_Serre_1977.Chap06.Proposition_6_6_3_2
import LinearRepresentations_Serre_1977.Chap06.Corollary_6_6_5_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators MonoidAlgebra Representation
open CategoryTheory

noncomputable section

universe u v

namespace Representation

section

variable {k G : Type u} [fieldK : Field k]
variable [groupG : Group G] [finiteG : Finite G]

local instance instFintypeGExercise_6_6_3_3 : Fintype G := Fintype.ofFinite G

section CharacterCentralElementDef

variable (V : Rep k G)

-- Proof sketch: the coefficient function `s ↦ V.ρ.character s⁻¹` is constant on conjugacy
-- classes because characters are class functions, so the corresponding group-algebra element
-- commutes with each basis element `MonoidAlgebra.of k G t`.
/-- The central group-algebra element attached to the character of `V` by LinearRepresentations_Serre_1977's formula. -/
theorem characterCentralElement_mem_center :
    ((Module.finrank k V : k) / Nat.card G) •
        ∑ s : G, V.ρ.character s⁻¹ • MonoidAlgebra.of k G s ∈
      Subalgebra.center k (k[G]) := by
  let f : G → k := fun s ↦ ((Module.finrank k V : k) / Nat.card G) * V.ρ.character s⁻¹
  have hf : IsClassFunction f := by
    -- The inverse character remains constant on conjugacy classes.
    refine ⟨?_⟩
    intro a b hab
    rcases isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hab) with ⟨g, hg⟩
    calc
      ((Module.finrank k V : k) / Nat.card G) * V.ρ.character a⁻¹
          =
        ((Module.finrank k V : k) / Nat.card G) * V.ρ.character (g * a⁻¹ * g⁻¹) := by
            rw [(V.ρ.char_conj a⁻¹ g).symm]
      _ = ((Module.finrank k V : k) / Nat.card G) * V.ρ.character b⁻¹ := by
            have hinv : g * a⁻¹ * g⁻¹ = b⁻¹ := by
              rw [← hg]
              simp [mul_assoc]
            simp [hinv]
  set z : k[G] := Finsupp.equivFunOnFinite.symm f
  have hcoeff :
      z = ((Module.finrank k V : k) / Nat.card G) •
        ∑ s : G, V.ρ.character s⁻¹ • MonoidAlgebra.of k G s := by
    calc
      z
          = ∑ s : G,
              ((((Module.finrank k V : k) / Nat.card G) * V.ρ.character s⁻¹) •
                MonoidAlgebra.of k G s) := by
              simpa [z, MonoidAlgebra.of, f] using
                (Finsupp.equivFunOnFinite_symm_eq_sum f)
      _ = ((Module.finrank k V : k) / Nat.card G) •
            ∑ s : G, V.ρ.character s⁻¹ • MonoidAlgebra.of k G s := by
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro s hs
            simp [mul_smul]
  have hz : z ∈ Subalgebra.center k (k[G]) := by
    -- A class function gives coefficients that commute with every group-algebra element.
    have hzsub : z ∈ Subsemiring.center k[G] := by
      rw [Subsemiring.mem_center_iff]
      intro y
      ext h
      rw [MonoidAlgebra.mul_apply_left, MonoidAlgebra.mul_apply_right]
      rw [Finsupp.sum, Finsupp.sum]
      refine Finset.sum_congr rfl ?_
      intro a ha
      have hcomm : f (a⁻¹ * h) = f (h * a⁻¹) := by
        have hmk : ConjClasses.mk (a⁻¹ * h) = ConjClasses.mk (h * a⁻¹) := by
          exact ConjClasses.mk_eq_mk_iff_isConj.mpr <| isConj_iff.mpr ⟨h, by simp [mul_assoc]⟩
        exact hf.factorsThrough hmk
      simpa [mul_comm] using congrArg (fun t : k ↦ y a * t) hcomm
    simpa using hzsub
  simpa [hcoeff] using hz

variable [finV : FiniteDimensional k V]

/-- The character-theoretic central element of `k[G]` attached to `V`. Without irreducibility, it
need not be primitive or idempotent. -/
def characterCentralElement : Subalgebra.center k (k[G]) :=
  ⟨((Module.finrank k V : k) / Nat.card G) •
      ∑ s : G, V.ρ.character s⁻¹ • MonoidAlgebra.of k G s,
    characterCentralElement_mem_center V⟩

end CharacterCentralElementDef

section CompleteFamilyExistence

variable [IsAlgClosed k] [Invertible (Nat.card G : k)]

/-- Helper for Exercise 6-6.3-3: under the Maschke hypotheses, one can choose a complete
pairwise nonisomorphic family of finite-dimensional representations in `Rep`. -/
theorem exists_complete_pairwise_nonisomorphic_rep_family :
    ∃ (ι : Type u) (_ : Fintype ι) (π : ι → Rep.{u, u, u} k G)
      (_ : ∀ i, FiniteDimensional k (π i)),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ) := by
  classical
  letI : NeZero (Nat.card G : k) := ⟨Invertible.ne_zero (Nat.card G : k)⟩
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :=
    exists_isInternal_irreducible_subrepresentations (ρ := leftRegular k G)
  let hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  let r : Setoid κ :=
    { r := fun i j ↦ Nonempty ((σ i).toRepresentation.Equiv (σ j).toRepresentation)
      iseqv :=
        ⟨fun i ↦ ⟨Representation.Equiv.refl _⟩,
          fun {i j} hij ↦ by
            rcases hij with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {i j l} hij hjl ↦ by
            rcases hij with ⟨eij⟩
            rcases hjl with ⟨ejl⟩
            exact ⟨eij.trans ejl⟩⟩ }
  let ι : Type u := Quotient r
  letI : Finite ι := by
    refine Finite.of_surjective (fun i : κ ↦ (⟦i⟧ : ι)) ?_
    intro q
    exact ⟨Quotient.out q, Quotient.out_eq q⟩
  letI : Fintype ι := Fintype.ofFinite ι
  let πfd : ι → FDRep k G := fun q ↦ FDRep.of ((σ (Quotient.out q)).toRepresentation)
  have hπfd_pairwise : PairwiseNonisomorphic πfd := by
    -- Distinct quotient classes cannot label isomorphic chosen representatives.
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hrel :
        Nonempty
          (Representation.Equiv
            ((σ (Quotient.out q)).toRepresentation)
            ((σ (Quotient.out q')).toRepresentation)) := by
      simpa [πfd] using
        (show Nonempty (Representation.Equiv ((πfd q).ρ) ((πfd q').ρ)) from
          ⟨Representation.equivOfIso ((forget₂ (FDRep k G) (Rep k G)).mapIso e)⟩)
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := Quotient.sound hrel
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπfd_simple (q : ι) : Simple (πfd q) := by
    -- Each chosen representative is one of the irreducible summands of the regular
    -- representation.
    letI : Representation.IsIrreducible (πfd q).ρ := by
      simpa [πfd] using hσ_irr (Quotient.out q)
    exact FDRep.simple_of_isIrreducible (πfd q)
  let S : ι → Finset κ :=
    fun q ↦ Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (πfd q).ρ)
  let dimσ : κ → Nat := fun j ↦ Module.finrank k (σ j).toSubmodule
  have hS_disjoint : Pairwise fun q q' ↦ Disjoint (S q) (S q') := by
    intro q q' hqq'
    refine Finset.disjoint_left.mpr fun j hj hj' ↦ ?_
    rcases (Finset.mem_filter.mp hj).2 with ⟨eqj⟩
    rcases (Finset.mem_filter.mp hj').2 with ⟨eqj'⟩
    exact hπfd_pairwise hqq' <| ⟨(eqj.symm.trans eqj').toFDRepIso⟩
  have hS_card (q : ι) : (S q).card = Module.finrank k (πfd q) := by
    have hmult :
        Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv (πfd q).ρ) } =
          Module.finrank k (πfd q) := by
      letI : Representation.IsIrreducible (πfd q).ρ := by
        exact FDRep.isIrreducible_of_simple (πfd q)
      simpa using
        leftRegular_irreducible_multiplicity_eq_finrank σ hinternal hσ_irr (πfd q).ρ
          inferInstance
    have hcard :
        Fintype.card { j // Nonempty ((σ j).toRepresentation.Equiv (πfd q).ρ) } = (S q).card := by
      rw [show S q = Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (πfd q).ρ) by
        rfl]
      rw [Fintype.card_of_subtype
        (Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (πfd q).ρ))]
      intro j
      simp
    exact hcard.symm.trans <| by
      simpa [Nat.card_eq_fintype_card] using hmult
  have hS_sum (q : ι) : Finset.sum (S q) dimσ = Module.finrank k (πfd q) ^ 2 := by
    calc
      Finset.sum (S q) dimσ = Finset.sum (S q) (fun _j ↦ Module.finrank k (πfd q)) := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
        exact e.toLinearEquiv.finrank_eq
      _ = (S q).card * Module.finrank k (πfd q) := by
            simp
      _ = Module.finrank k (πfd q) ^ 2 := by
            rw [hS_card, pow_two]
  have hcover :
      Finset.univ.biUnion S = (Finset.univ : Finset κ) := by
    apply Finset.ext
    intro j
    constructor
    · intro _
      simp
    · intro hj
      have hj_mem : j ∈ S (⟦j⟧ : ι) := by
        refine Finset.mem_filter.mpr ?_
        constructor
        · simp
        · rcases Quotient.exact (Quotient.out_eq (⟦j⟧ : ι)) with ⟨e⟩
          exact ⟨e.symm⟩
      exact Finset.mem_biUnion.mpr ⟨(⟦j⟧ : ι), Finset.mem_univ _, hj_mem⟩
  have htotal_eq_card : Finset.sum (Finset.univ : Finset κ) dimσ = Nat.card G := by
    letI := DirectSum.IsInternal.chooseDecomposition (fun j ↦ (σ j).toSubmodule) hinternal
    letI : ∀ j : κ, Module.Free k (σ j).toSubmodule := fun j ↦
      Module.Free.of_divisionRing k (σ j).toSubmodule
    let e := (DirectSum.decomposeLinearEquiv (fun j ↦ (σ j).toSubmodule)).symm
    calc
      Finset.sum (Finset.univ : Finset κ) dimσ = Module.finrank k (G →₀ k) := by
        symm
        calc
          Module.finrank k (G →₀ k) =
            Module.finrank k (DirectSum κ fun j ↦ (σ j).toSubmodule) := by
              exact e.finrank_eq.symm
          _ = Finset.sum (Finset.univ : Finset κ) dimσ := by
              dsimp [dimσ]
              exact Module.finrank_directSum (R := k) (M := fun j ↦ (σ j).toSubmodule)
      _ = Nat.card G := by
          rw [Nat.card_eq_fintype_card]
          exact Module.finrank_finsupp_self k
  have hπ_sum : ∑ q : ι, Module.finrank k (πfd q) ^ 2 = Nat.card G := by
    calc
      ∑ q : ι, Module.finrank k (πfd q) ^ 2 = ∑ q : ι, Finset.sum (S q) dimσ := by
        refine Finset.sum_congr rfl fun q _ ↦ (hS_sum q).symm
      _ = Finset.sum (Finset.univ.biUnion S) dimσ := by
          symm
          exact Finset.sum_biUnion fun q _ q' _ hqq' ↦ hS_disjoint hqq'
      _ = Finset.sum (Finset.univ : Finset κ) dimσ := by
          rw [hcover]
      _ = Nat.card G := htotal_eq_card
  have hπfd_complete : IsCompleteIrreducibleFamily πfd := by
    exact isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card
      πfd hπfd_simple hπfd_pairwise hπ_sum
  let π : ι → Rep.{u, u, u} k G := fun q ↦ (forget₂ (FDRep k G) (Rep k G)).obj (πfd q)
  have hπ_fd : ∀ q, FiniteDimensional k (π q) := by
    intro q
    simpa [π] using (inferInstance : FiniteDimensional k (πfd q))
  have hπ_pairwise : PairwiseNonisomorphic π := by
    intro q q' hqq' hIso
    apply hπfd_pairwise hqq'
    rcases hIso with ⟨e⟩
    refine ⟨?_⟩
    simpa [π] using (Representation.equivOfIso e).toFDRepIso
  have hπ_complete : IsCompleteIrreducibleFamily (fun q ↦ FDRep.of (π q).ρ) := by
    simpa [π] using hπfd_complete
  exact ⟨ι, inferInstance, π, hπ_fd, hπ_pairwise, hπ_complete⟩

end CompleteFamilyExistence

section CharacterCentralElement

variable [charZeroK : CharZero k] [algClosedK : IsAlgClosed k]
variable [invCardG : Invertible (Nat.card G : k)]

attribute [local instance] Classical.propDecidable

section IsoFacts

variable {X Y : Rep.{u, u, u} k G}
variable [finX : FiniteDimensional k X] [finY : FiniteDimensional k Y]

omit finiteG charZeroK invCardG
/-- Helper for Exercise 6-6.3-3: isomorphic irreducible representations have the same central
character on the center of `k[G]`. -/
theorem centralCharacter_eq_of_nonempty_iso
    (hXY : Nonempty (X ≅ Y)) (hX : X.ρ.IsIrreducible) (hY : Y.ρ.IsIrreducible) :
    ω[X.ρ] = ω[Y.ρ] := by
  classical
  rcases hXY with ⟨e⟩
  let eρ : X.ρ.Equiv Y.ρ := Representation.equivOfIso e
  have hcomm : ∀ a : k[G], ∀ x : X, eρ (X.ρ.asAlgebraHom a x) = Y.ρ.asAlgebraHom a (eρ x) := by
    intro a
    refine MonoidAlgebra.induction_on
      (p := fun a : k[G] ↦ ∀ x : X, eρ (X.ρ.asAlgebraHom a x) = Y.ρ.asAlgebraHom a (eρ x))
      a ?_ ?_ ?_
    · intro g x
      simpa [Representation.asAlgebraHom_of] using
        congrArg (fun f : X →ₗ[k] Y ↦ f x) (eρ.isIntertwining' g)
    · intro a b ha hb x
      simp [ha x, hb x]
    · intro r a ha x
      simp [ha x]
  ext u
  letI : X.ρ.IsIrreducible := hX
  letI : Y.ρ.IsIrreducible := hY
  letI : Nontrivial X := not_subsingleton_iff_nontrivial.mp fun hXsub ↦
    (show (⊥ : Subrepresentation X.ρ) ≠ ⊤ from IsSimpleOrder.bot_ne_top) <|
      top_unique <| by
        intro x hx
        change x = 0
        exact hXsub.elim x 0
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  have hx' : eρ x ≠ 0 := by
    intro hzero
    apply hx
    have hzero' : eρ.toLinearEquiv x = eρ.toLinearEquiv 0 := by
      simpa using hzero
    simpa using eρ.toLinearEquiv.injective hzero'
  have hXu :
      X.ρ.asAlgebraHom u x = ω[X.ρ] u • x := by
    simpa using
      congrArg (fun f : Module.End k X ↦ f x)
        (asAlgebraHom_center_eq_centralCharacter_smul_id X.ρ u)
  have hYu :
      Y.ρ.asAlgebraHom u (eρ x) = ω[Y.ρ] u • eρ x := by
    simpa using
      congrArg (fun f : Module.End k Y ↦ f (eρ x))
        (asAlgebraHom_center_eq_centralCharacter_smul_id Y.ρ u)
  have hscalar : ω[X.ρ] u • eρ x = ω[Y.ρ] u • eρ x := by
    -- Conjugate the central action across the representation isomorphism and compare the scalar
    -- actions furnished by Schur's lemma.
    calc
      ω[X.ρ] u • eρ x = eρ (ω[X.ρ] u • x) := by simp
      _ = eρ (X.ρ.asAlgebraHom u x) := by rw [hXu]
      _ = Y.ρ.asAlgebraHom u (eρ x) := hcomm (u : k[G]) x
      _ = ω[Y.ρ] u • eρ x := hYu
  have hsub : (ω[X.ρ] u - ω[Y.ρ] u) • eρ x = 0 := by
    rw [sub_smul, hscalar, sub_self]
  exact sub_eq_zero.mp <| by
    rcases smul_eq_zero.mp hsub with hzero | hzero
    · exact hzero
    · exact (hx' hzero).elim

include finiteG charZeroK invCardG

omit charZeroK algClosedK invCardG finX finY
/-- Helper for Exercise 6-6.3-3: isomorphic representations give the same character-theoretic
central element. -/
theorem characterCentralElement_eq_of_nonempty_iso
    (hXY : Nonempty (X ≅ Y)) :
    characterCentralElement X = characterCentralElement Y := by
  rcases hXY with ⟨e⟩
  have hfinrank : Module.finrank k X = Module.finrank k Y :=
    (Representation.equivOfIso e).toLinearEquiv.finrank_eq
  have hchar : X.ρ.character = Y.ρ.character :=
    Representation.char_iso (Representation.equivOfIso e)
  apply Subtype.ext
  -- Compare coefficients after transporting both the degree and the character across the
  -- isomorphism.
  ext s
  simp [characterCentralElement, MonoidAlgebra.of, hfinrank, hchar]

include charZeroK algClosedK invCardG finX finY

end IsoFacts

omit groupG finiteG charZeroK algClosedK
/-- Helper for Exercise 6-6.3-3: any natural-number divisor of `|G|` remains nonzero in `k`
when `|G|` is invertible in `k`. -/
lemma nat_cast_ne_zero_of_dvd_group_order
    {n : ℕ} (hn : n ∣ Nat.card G) :
    (n : k) ≠ 0 := by
  rcases hn with ⟨m, hm⟩
  intro hzero
  have hcard_zero : (Nat.card G : k) = 0 := by
    -- Cast the divisibility witness into `k`, then the vanishing of `n` forces `|G|` to vanish.
    calc
      (Nat.card G : k) = ((n * m : ℕ) : k) := by
        rw [hm]
      _ = (n : k) * (m : k) := by
        rw [Nat.cast_mul]
      _ = 0 := by simp [hzero]
  exact Invertible.ne_zero (Nat.card G : k) hcard_zero

include groupG finiteG charZeroK algClosedK

section IrreducibleFacts

variable {X Y : Rep.{u, u, u} k G}
variable [finX : FiniteDimensional k X] [finY : FiniteDimensional k Y]

omit finX
/-- Helper for Exercise 6-6.3-3: an irreducible representation has nonzero degree in the
coefficient field. -/
lemma finrank_cast_ne_zero_of_is_irreducible
    (hX : X.ρ.IsIrreducible) :
    (Module.finrank k X : k) ≠ 0 := by
  -- LinearRepresentations_Serre_1977's later divisibility theorem gives `dim X ∣ |G|`; since `|G|` is invertible in
  -- `k`, this degree is nonzero in `k`.
  letI : X.ρ.IsIrreducible := hX
  have hdiv : Module.finrank k X ∣ Nat.card G := finrank_dvd_card X.ρ
  exact nat_cast_ne_zero_of_dvd_group_order (k := k) (G := G) hdiv

include finX

omit finiteG charZeroK algClosedK invCardG
/-- Helper for Exercise 6-6.3-3: an isomorphism in `Rep` is equivalent to an equivalence of the
underlying representations. -/
lemma nonempty_iso_iff_nonempty_rho_equiv :
    Nonempty (X ≅ Y) ↔ Nonempty (X.ρ.Equiv Y.ρ) := by
  constructor
  · intro hXY
    rcases hXY with ⟨e⟩
    -- Forget the categorical isomorphism to its intertwining equivalence.
    exact ⟨Representation.equivOfIso e⟩
  · intro hXY
    rcases hXY with ⟨e⟩
    -- Repackage the representation equivalence through the finite-dimensional owner `FDRep`.
    simpa using ⟨(forget₂ (FDRep k G) (Rep k G)).mapIso e.toFDRepIso⟩

include finiteG charZeroK algClosedK invCardG

/-- Helper for Exercise 6-6.3-3: LinearRepresentations_Serre_1977's explicit central element acts on an irreducible
representation by the normalized intertwining multiplicity. -/
lemma centralCharacter_characterCentralElement_eq_dim_ratio_mul_finrank_intertwining
    (hX : X.ρ.IsIrreducible) (_hY : Y.ρ.IsIrreducible) :
    ω[X.ρ] (characterCentralElement Y) =
      ((Module.finrank k Y : k) / (Module.finrank k X : k)) *
        Module.finrank k (Y.ρ.IntertwiningMap X.ρ) := by
  have hfinrankX := finrank_cast_ne_zero_of_is_irreducible (X := X) hX
  have hcoeff :
      ∀ s : G,
        ((characterCentralElement Y : k[G]) s) =
          ((Module.finrank k Y : k) / Nat.card G) * Y.ρ.character s⁻¹ := by
    intro s
    let a : k := ((Module.finrank k Y : k) / Nat.card G)
    have hsingle :
        (∑ t : G, (Y.ρ.character t⁻¹ • MonoidAlgebra.of k G t : k[G])) s =
          Y.ρ.character s⁻¹ := by
      have hsum_single :
          (∑ t : G, (Y.ρ.character t⁻¹ • MonoidAlgebra.of k G t : k[G])) =
            Finsupp.equivFunOnFinite.symm (fun t : G ↦ Y.ρ.character t⁻¹) := by
        -- Repackage the source-facing sum as the canonical finitely supported function.
        simpa [MonoidAlgebra.of] using
          (Finsupp.equivFunOnFinite_symm_eq_sum (fun t : G ↦ Y.ρ.character t⁻¹)).symm
      -- Read off the coefficient at `s` from the packaged finitely supported function.
      simpa using congrArg (fun z : k[G] ↦ z s) hsum_single
    -- Evaluate the explicit coefficient of LinearRepresentations_Serre_1977's central element at `s`.
    change (a * (∑ t : G, (Y.ρ.character t⁻¹ • MonoidAlgebra.of k G t : k[G])) s =
      a * Y.ρ.character s⁻¹)
    rw [hsingle]
  have hsum :
      ∑ s : G,
          (((Module.finrank k Y : k) / Nat.card G) * Y.ρ.character s⁻¹) *
            X.ρ.character s =
        ((Module.finrank k Y : k) / Nat.card G) *
          ∑ s : G, X.ρ.character s * Y.ρ.character s⁻¹ := by
    calc
      ∑ s : G,
          (((Module.finrank k Y : k) / Nat.card G) * Y.ρ.character s⁻¹) *
            X.ρ.character s
        =
          ∑ s : G,
            ((Module.finrank k Y : k) / Nat.card G) *
              (X.ρ.character s * Y.ρ.character s⁻¹) := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            ring
      _ =
          ((Module.finrank k Y : k) / Nat.card G) *
            ∑ s : G, X.ρ.character s * Y.ρ.character s⁻¹ := by
            symm
            rw [Finset.mul_sum]
  -- Route correction: rewrite LinearRepresentations_Serre_1977's element into the canonical character pairing first, and
  -- only then invoke the owner theorem identifying that pairing with an intertwining dimension.
  rw [centralCharacter_apply_eq_sum_character (ρ := X.ρ)
    (u := characterCentralElement Y) hfinrankX]
  calc
    (Module.finrank k X : k)⁻¹ *
        ∑ s : G, ((characterCentralElement Y : k[G]) s) * X.ρ.character s
      =
        (Module.finrank k X : k)⁻¹ *
          ∑ s : G,
            (((Module.finrank k Y : k) / Nat.card G) * Y.ρ.character s⁻¹) *
              X.ρ.character s := by
          -- Expand the coefficients of `characterCentralElement Y`.
          refine congrArg (fun z : k ↦ (Module.finrank k X : k)⁻¹ * z) ?_
          refine Finset.sum_congr rfl ?_
          intro s hs
          rw [hcoeff s]
    _ =
        (Module.finrank k X : k)⁻¹ *
          (((Module.finrank k Y : k) / Nat.card G) *
            ∑ s : G, X.ρ.character s * Y.ρ.character s⁻¹) := by
          -- Pull the scalar factor out of the finite sum and commute the character factors into
          -- the owner-theorem order.
          rw [hsum]
    _ =
        ((Module.finrank k Y : k) / (Module.finrank k X : k)) *
          ((Nat.card G : k)⁻¹ * ∑ s : G, X.ρ.character s * Y.ρ.character s⁻¹) := by
          -- Isolate the normalized pairing of `Y` with `X`.
          simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    _ =
        ((Module.finrank k Y : k) / (Module.finrank k X : k)) *
          Module.finrank k (Y.ρ.IntertwiningMap X.ρ) := by
          rw [Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := Y.ρ) (σ := X.ρ)]

omit finX finY
/-- Helper for Exercise 6-6.3-3: isomorphic irreducible representations have the same degree, so
the degree ratio in LinearRepresentations_Serre_1977's formula is `1`. -/
lemma finrank_ratio_eq_one_of_nonempty_iso
    (hX : X.ρ.IsIrreducible) (hXY : Nonempty (X ≅ Y)) :
    ((Module.finrank k Y : k) / (Module.finrank k X : k)) = 1 := by
  rcases hXY with ⟨e⟩
  have hfinrank : Module.finrank k Y = Module.finrank k X :=
    (Representation.equivOfIso e).toLinearEquiv.finrank_eq.symm
  have hfinrankX := finrank_cast_ne_zero_of_is_irreducible (X := X) hX
  -- Transport dimension across the isomorphism and cancel the nonzero denominator.
  rw [hfinrank, div_self hfinrankX]

include finX finY

/-- Helper for Exercise 6-6.3-3: the central character of an irreducible representation evaluates
LinearRepresentations_Serre_1977's central element by the Kronecker delta on isomorphism classes. -/
theorem centralCharacter_characterCentralElement_eq_ite_of_irreducible
    (hX : X.ρ.IsIrreducible) (hY : Y.ρ.IsIrreducible) :
    ω[X.ρ] (characterCentralElement Y) = if Nonempty (X ≅ Y) then 1 else 0 := by
  have hpair :=
    centralCharacter_characterCentralElement_eq_dim_ratio_mul_finrank_intertwining
      (X := X) (Y := Y) hX hY
  have hintertwining :
      Module.finrank k (Y.ρ.IntertwiningMap X.ρ) =
        if Nonempty (Y.ρ.Equiv X.ρ) then 1 else 0 := by
    -- Schur's lemma turns the intertwining multiplicity into the Kronecker delta.
    simpa using
      Representation.finrank_intertwiningMap_eq_ite_one_zero_of_isIrreducible
        Y.ρ hY X.ρ hX
  -- Execute the source proof's governing structure: explicit central element -> normalized
  -- pairing -> intertwining multiplicity -> Schur delta.
  rw [hpair, hintertwining]
  by_cases hXY : Nonempty (X ≅ Y)
  · have hYX : Nonempty (Y ≅ X) := by
      rcases hXY with ⟨e⟩
      exact ⟨e.symm⟩
    have hρ : Nonempty (Y.ρ.Equiv X.ρ) :=
      (nonempty_iso_iff_nonempty_rho_equiv (X := Y) (Y := X)).mp hYX
    have hratio :
        ((Module.finrank k Y : k) / (Module.finrank k X : k)) = 1 :=
      finrank_ratio_eq_one_of_nonempty_iso (X := X) (Y := Y) hX hXY
    -- On the isomorphic branch, Schur gives multiplicity `1` and the degree ratio cancels.
    simp [hXY, hρ, hratio]
  · have hρ : ¬ Nonempty (Y.ρ.Equiv X.ρ) := by
      intro hρ
      apply hXY
      have hYX : Nonempty (Y ≅ X) :=
        (nonempty_iso_iff_nonempty_rho_equiv (X := Y) (Y := X)).mpr hρ
      rcases hYX with ⟨e⟩
      exact ⟨e.symm⟩
    -- In the nonisomorphic branch, Schur's lemma already forces the scalar to vanish.
    simp [hXY, hρ]

end IrreducibleFacts

end CharacterCentralElement

section

variable {ι : Type v}
variable (π : ι → Rep k G)
variable [∀ i, FiniteDimensional k (π i)]

section CompleteFamily

variable [CharZero k] [IsAlgClosed k] [Invertible (Nat.card G : k)]

variable (hπ_pairwise : PairwiseNonisomorphic π)
variable (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ))

attribute [local instance] Classical.propDecidable

-- Proof sketch: transport the standard basis of `ι → k` back along the central-character algebra
-- equivalence from Proposition `6-6.3-2`, then identify the inverse image of `Pi.basisFun k ι i`
-- with LinearRepresentations_Serre_1977's explicit central element using the character formula of Proposition `6-6.3-1`.
/-- Exercise 6-6.3-3: under the canonical central-character algebra equivalence, the inverse image
of the `i`-th standard basis vector is the central primitive idempotent attached to `π i`. -/
theorem centralCharacterFamilyAlgEquiv_symm_basisFun
    (i : ι) :
    let _ : Finite ι := IsCompleteIrreducibleFamily.finite_index_of_rep π hπ_complete hπ_pairwise
    (centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete).symm (Pi.basisFun k ι i) =
      characterCentralElement (π i) := by
  classical
  let e := centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index_of_rep π hπ_complete hπ_pairwise
  apply e.injective
  -- Push both sides through the central-character equivalence and read the coordinates.
  ext j
  letI : (π i).ρ.IsIrreducible :=
    IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete i
  letI : (π j).ρ.IsIrreducible :=
    IsCompleteIrreducibleFamily.isIrreducible_of_rep hπ_complete j
  by_cases hji : j = i
  · subst hji
    simp [e, centralCharacter_characterCentralElement_eq_ite_of_irreducible]
  · have hnot : ¬ Nonempty (π j ≅ π i) := hπ_pairwise hji
    simp [e, hji, hnot, centralCharacter_characterCentralElement_eq_ite_of_irreducible]

attribute [simp] centralCharacterFamilyAlgEquiv_symm_basisFun

-- Proof sketch: LinearRepresentations_Serre_1977's elements `p_i` are exactly the inverse images of the standard basis
-- vectors under Proposition `6-6.3-2`, so transporting `Pi.basisFun k ι` gives a basis of the
-- center.
/-- A basis statement for Exercise 6-6.3-3: for a complete pairwise nonisomorphic irreducible
family, the corresponding central primitive idempotents form a basis of the center of `k[G]`. -/
theorem centralPrimitiveIdempotents_form_basis :
    (hπ_pairwise : PairwiseNonisomorphic π) →
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) →
    ∃ b : Module.Basis ι k (Subalgebra.center k (k[G])),
      ∀ i, b i = characterCentralElement (π i) := by
  intro hπ_pairwise hπ_complete
  classical
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index_of_rep π hπ_complete hπ_pairwise
  refine ⟨(Pi.basisFun k ι).map
      (centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete).symm.toLinearEquiv, ?_⟩
  -- Read each transported basis vector through the source-faithful identification above.
  intro i
  simpa using
    (centralCharacterFamilyAlgEquiv_symm_basisFun
      (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete) i)

-- Proof sketch: transport the finite sum through the center-character algebra equivalence. The sum
-- of the standard basis vectors in `ι → k` is the constant function `1`, which corresponds to the
-- unit of the center.
/-- The sum of the central primitive idempotents is the unit of the center of `k[G]`. -/
theorem sum_centralPrimitiveIdempotent :
    (hπ_pairwise : PairwiseNonisomorphic π) →
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of (π i).ρ)) →
    ∑ᶠ i, characterCentralElement (π i) = 1 := by
  intro hπ_pairwise hπ_complete
  classical
  let e := centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index_of_rep π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  have hsupp : Function.HasFiniteSupport (fun i : ι ↦ characterCentralElement (π i)) :=
    Set.toFinite _
  apply e.injective
  -- Transport the finite sum to the product algebra, where the summands are basis vectors.
  rw [finsum_eq_sum _ hsupp, map_sum]
  simp_rw [← centralCharacterFamilyAlgEquiv_symm_basisFun
    (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)]
  ext j
  simp [e]

end CompleteFamily

section Irreducible

variable [CharZero k] [IsAlgClosed k] [Invertible (Nat.card G : k)]
variable (V W : Rep.{u, u, u} k G)
variable [FiniteDimensional k V] [FiniteDimensional k W]

attribute [local instance] Classical.propDecidable

-- Proof sketch: combine `asAlgebraHom_center_eq_centralCharacter_smul_id` with the evaluation of
-- `ω[V.ρ] (characterCentralElement V)` coming from the canonical normalized character-pairing
-- theorem over `[Invertible (Nat.card G : k)]`; the self-pairing of an irreducible character is
-- `1`.
/-- For an irreducible representation over an algebraically closed field in which `|G|` is
invertible, the associated central element acts by the identity on that representation. -/
theorem asAlgebraHom_centralPrimitiveIdempotent_eq_id
    (hV : V.ρ.IsIrreducible) :
    V.ρ.asAlgebraHom (characterCentralElement V : k[G]) = LinearMap.id := by
  letI : V.ρ.IsIrreducible := hV
  -- Route correction: compute the central-character scalar first, then translate it to the action.
  rw [asAlgebraHom_center_eq_centralCharacter_smul_id V.ρ (characterCentralElement V)]
  have hω :=
    centralCharacter_characterCentralElement_eq_ite_of_irreducible
      (X := V) (Y := V) hV hV
  simp at hω
  simp [hω]

-- Proof sketch: the central element attached to `V` acts by the identity on the irreducible
-- representation `V`; since `characterCentralElement V` lies in the center, idempotence follows by
-- comparing the two central actions on the regular representation.
/-- Over an algebraically closed field in which `|G|` is invertible, each irreducible central
primitive idempotent satisfies `p^2 = p`. -/
theorem centralPrimitiveIdempotent_mul_self
    (hV : V.ρ.IsIrreducible) :
    characterCentralElement V * characterCentralElement V = characterCentralElement V := by
  classical
  obtain ⟨ι, _, π, hπ_fd, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_rep_family (k := k) (G := G)
  let e := centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index_of_rep π hπ_complete hπ_pairwise
  obtain ⟨i, hi_fd⟩ :=
    IsCompleteIrreducibleFamily.exists_iso_of_representation
      (fun i ↦ FDRep.of (π i).ρ) hπ_complete V.ρ inferInstance
  have hi : Nonempty (V ≅ π i) := by
    rcases hi_fd with ⟨eFD⟩
    exact ⟨(forget₂ (FDRep k G) (Rep k G)).mapIso eFD⟩
  have hV_eq : characterCentralElement V = characterCentralElement (π i) :=
    characterCentralElement_eq_of_nonempty_iso (X := V) (Y := π i) hi
  -- Transport LinearRepresentations_Serre_1977's element to the canonical basis vector and use coordinatewise idempotence.
  rw [hV_eq]
  apply e.injective
  rw [map_mul]
  simp_rw [show characterCentralElement (π i) = e.symm (Pi.basisFun k ι i) by
    symm
    exact centralCharacterFamilyAlgEquiv_symm_basisFun
      (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete) i]
  ext j
  by_cases hji : j = i
  · subst hji
    simp
  · simp [Pi.basisFun_apply, hji]

-- Proof sketch: apply the nonisomorphic irreducible character orthogonality relation to the
-- central element attached to `W`; it acts by zero on `V`, so the product vanishes.
/-- Over an algebraically closed field in which `|G|` is invertible, central primitive
idempotents attached to nonisomorphic irreducibles are orthogonal. -/
theorem centralPrimitiveIdempotent_mul_eq_zero_of_not_isomorphic
    (hV : V.ρ.IsIrreducible) (hW : W.ρ.IsIrreducible) (hVW : ¬ Nonempty (V ≅ W)) :
    characterCentralElement V * characterCentralElement W = 0 := by
  classical
  obtain ⟨ι, _, π, hπ_fd, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_rep_family (k := k) (G := G)
  let e := centralCharacterFamilyAlgEquiv π hπ_pairwise hπ_complete
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index_of_rep π hπ_complete hπ_pairwise
  obtain ⟨i, hi_fd⟩ :=
    IsCompleteIrreducibleFamily.exists_iso_of_representation
      (fun i ↦ FDRep.of (π i).ρ) hπ_complete V.ρ inferInstance
  obtain ⟨j, hj_fd⟩ :=
    IsCompleteIrreducibleFamily.exists_iso_of_representation
      (fun i ↦ FDRep.of (π i).ρ) hπ_complete W.ρ inferInstance
  have hi : Nonempty (V ≅ π i) := by
    rcases hi_fd with ⟨eFD⟩
    exact ⟨(forget₂ (FDRep k G) (Rep k G)).mapIso eFD⟩
  have hj : Nonempty (W ≅ π j) := by
    rcases hj_fd with ⟨eFD⟩
    exact ⟨(forget₂ (FDRep k G) (Rep k G)).mapIso eFD⟩
  have hij : i ≠ j := by
    intro hij_eq
    subst hij_eq
    rcases hi with ⟨eV⟩
    rcases hj with ⟨eW⟩
    exact hVW ⟨eV.trans eW.symm⟩
  have hV_eq : characterCentralElement V = characterCentralElement (π i) :=
    characterCentralElement_eq_of_nonempty_iso (X := V) (Y := π i) hi
  have hW_eq : characterCentralElement W = characterCentralElement (π j) :=
    characterCentralElement_eq_of_nonempty_iso (X := W) (Y := π j) hj
  -- Transport both factors to distinct coordinate basis vectors and multiply pointwise.
  rw [hV_eq, hW_eq]
  apply e.injective
  rw [map_mul, map_zero]
  simp_rw [show characterCentralElement (π i) = e.symm (Pi.basisFun k ι i) by
    symm
    exact centralCharacterFamilyAlgEquiv_symm_basisFun
      (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete) i]
  simp_rw [show characterCentralElement (π j) = e.symm (Pi.basisFun k ι j) by
    symm
    exact centralCharacterFamilyAlgEquiv_symm_basisFun
      (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete) j]
  ext x
  by_cases hxi : x = i
  · subst hxi
    simp [Pi.basisFun_apply, hij]
  · by_cases hxj : x = j
    · subst hxj
      simp [Pi.basisFun_apply, hij]
    · simp [Pi.basisFun_apply, hxi, hxj]

-- Proof sketch: expand `characterCentralElement W` and identify the resulting scalar with the
-- normalized pairing of the irreducible characters of `V` and `W`; the canonical owner theorems
-- for that pairing give `1` on an isomorphism class and `0` otherwise.
/-- The central character of an irreducible representation takes the central element of `W` to `1`
on its own isomorphism class and to `0` on all other irreducible classes. -/
theorem centralCharacter_centralPrimitiveIdempotent
    (hV : V.ρ.IsIrreducible) (hW : W.ρ.IsIrreducible) :
    ω[V.ρ] (characterCentralElement W) =
      if Nonempty (V ≅ W) then 1 else 0 := by
  -- This is exactly the character-orthogonality computation proved above.
  simpa using
    centralCharacter_characterCentralElement_eq_ite_of_irreducible
      (X := V) (Y := W) hV hW

end Irreducible

end

end

end Representation
