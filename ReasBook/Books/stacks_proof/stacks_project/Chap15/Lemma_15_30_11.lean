import Mathlib
import StacksProject_2024.Chap15.Definition_15_30_1
import StacksProject_2024.Chap15.Lemma_15_90_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace Ideal

theorem ofList_ofFn_eq_span_range {A : Type u} [CommRing A] {n : ℕ} (f : Fin n → A) :
    Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) := by
  ext x
  simp [Ideal.ofList, List.mem_ofFn', Set.range]

end Ideal

namespace RingTheory.Sequence

variable {A : Type u} [CommRing A]

/-- Helper for Lemma 15.30.11: the owner `H_1`-regularity predicate is equivalent to vanishing of
the source-facing first Koszul homology object `koszulH1`. -/
private theorem isH1RegularSequence_iff_isZero_koszulH1_local {r : ℕ} (s : Fin r → A) :
    IsH1RegularSequence s ↔ CategoryTheory.Limits.IsZero (koszulH1 s A) := by
  -- TODO: construct the canonical comparison
  -- `((K^•(s)).homology 1) ≅ koszulH1 s A`, then combine `isH1RegularSequence_iff` with
  -- `Iso.isZero_iff` across that isomorphism.
  sorry

/-- Helper for Lemma 15.30.11: `H_1`-regularity forces the source-facing quotient presentation of
the first Koszul homology to be subsingleton. -/
private theorem subsingleton_koszulH1Presentation_of_isH1RegularSequence {r : ℕ}
    (s : Fin r → A) (hs : IsH1RegularSequence s) :
    Subsingleton (koszulH1Presentation s A) := by
  -- Rewrite `H_1`-regularity as vanishing of the owner first Koszul homology object.
  have hzero : CategoryTheory.Limits.IsZero (koszulH1 s A) :=
    (isH1RegularSequence_iff_isZero_koszulH1_local s).1 hs
  -- Transport the vanishing statement to the explicit quotient presentation.
  have hzeroPresentation :
      CategoryTheory.Limits.IsZero (ModuleCat.of A (koszulH1Presentation s A)) :=
    (koszulH1IsoPresentation s A).isZero_iff.mp hzero
  exact (ModuleCat.isZero_iff_subsingleton).1 hzeroPresentation

/-- Helper for Lemma 15.30.11: every degree-one Koszul cycle of an `H_1`-regular family is a
diagonal boundary. -/
private theorem exists_diagonal_of_koszulFirstCycleCondition_of_isH1RegularSequence {r : ℕ}
    (s : Fin r → A) (hs : IsH1RegularSequence s) (x : Fin r → A)
    (hx : koszulFirstCycleCondition s A x) :
    ∃ a : A, koszulDiagonalLinearMap s A a = x := by
  let xCycle : koszulFirstCycles s A := ⟨x, (mem_koszulFirstCycles_iff s A x).2 hx⟩
  have hsub :
      Subsingleton (koszulH1Presentation s A) :=
    subsingleton_koszulH1Presentation_of_isH1RegularSequence s hs
  -- In the quotient presentation, every cycle class is already zero.
  have hxZero : (Submodule.Quotient.mk xCycle : koszulH1Presentation s A) = 0 :=
    hsub.elim _ _
  have hxMem :
      xCycle ∈ LinearMap.range (koszulDiagonalMap s A) := by
    rw [Submodule.Quotient.mk_eq_zero] at hxZero
    exact hxZero
  rcases hxMem with ⟨a, ha⟩
  -- Forget the cycle subtype to recover the ambient tuple equality.
  exact ⟨a, congrArg Subtype.val ha⟩

/-- Helper for Lemma 15.30.11: restricting an appended first cycle to the tail and quotienting by
the prefix ideal produces a quotient-side first cycle. -/
private theorem quotient_tail_cycle_of_append_cycle {n m : ℕ} (f : Fin n → A) (g : Fin m → A)
    (x : Fin (n + m) → A)
    (hx : koszulFirstCycleCondition (Fin.append f g) A x) :
    koszulFirstCycleCondition
      (fun j ↦ Ideal.Quotient.mk (Ideal.ofList (List.ofFn f)) (g j))
      (A ⧸ Ideal.ofList (List.ofFn f))
      (fun j ↦ Ideal.Quotient.mk (Ideal.ofList (List.ofFn f)) (x (Fin.natAdd n j))) := by
  intro j k
  -- Evaluate the appended cycle condition on tail indices and map the equality to the quotient.
  exact
    congrArg (Ideal.Quotient.mk (Ideal.ofList (List.ofFn f)))
      (by
        simpa [Fin.append, smul_eq_mul] using hx (Fin.natAdd n j) (Fin.natAdd n k))

/-- Helper for Lemma 15.30.11: lifting a quotient diagonal witness leaves the tail residual inside
the prefix ideal. -/
private theorem exists_tail_residual_mem_prefix_ideal {n m : ℕ} (f : Fin n → A) (g : Fin m → A)
    (x : Fin (n + m) → A) {bbar : A ⧸ Ideal.ofList (List.ofFn f)}
    (hb :
      koszulDiagonalLinearMap
          (fun j ↦ Ideal.Quotient.mk (Ideal.ofList (List.ofFn f)) (g j))
          (A ⧸ Ideal.ofList (List.ofFn f)) bbar =
        fun j ↦ Ideal.Quotient.mk (Ideal.ofList (List.ofFn f)) (x (Fin.natAdd n j))) :
    ∃ b : A, ∀ j, x (Fin.natAdd n j) - g j * b ∈ Ideal.ofList (List.ofFn f) := by
  rcases Ideal.Quotient.mk_surjective bbar with ⟨b, rfl⟩
  refine ⟨b, ?_⟩
  intro j
  have hbj :
      Ideal.Quotient.mk (Ideal.ofList (List.ofFn f)) (g j * b) =
        Ideal.Quotient.mk (Ideal.ofList (List.ofFn f)) (x (Fin.natAdd n j)) := by
    simpa [koszulDiagonalLinearMap, smul_eq_mul] using congrFun hb j
  have hzero :
      Ideal.Quotient.mk (Ideal.ofList (List.ofFn f)) (x (Fin.natAdd n j) - g j * b) = 0 := by
    rw [map_sub]
    rw [hbj, sub_self]
  exact (Ideal.Quotient.eq_zero_iff_mem).1 hzero

/-- Helper for Lemma 15.30.11: quotient-side `H_1`-regularity makes the tail of an appended
first cycle diagonal modulo the prefix ideal. -/
private theorem exists_tail_diagonal_lift_of_append_cycle {n m : ℕ} (f : Fin n → A)
    (g : Fin m → A)
    (hg : IsH1RegularSequence (fun j ↦ Ideal.Quotient.mk (Ideal.ofList (List.ofFn f)) (g j)))
    (x : Fin (n + m) → A)
    (hx : koszulFirstCycleCondition (Fin.append f g) A x) :
    ∃ b : A, ∀ j, x (Fin.natAdd n j) - g j * b ∈ Ideal.ofList (List.ofFn f) := by
  -- Pass to the quotient tail and use quotient-side `H_1`-regularity to make it diagonal.
  have htail :
      koszulFirstCycleCondition
        (fun j ↦ Ideal.Quotient.mk (Ideal.ofList (List.ofFn f)) (g j))
        (A ⧸ Ideal.ofList (List.ofFn f))
        (fun j ↦ Ideal.Quotient.mk (Ideal.ofList (List.ofFn f)) (x (Fin.natAdd n j))) :=
    quotient_tail_cycle_of_append_cycle f g x hx
  obtain ⟨bbar, hbbar⟩ :=
    exists_diagonal_of_koszulFirstCycleCondition_of_isH1RegularSequence
      (fun j ↦ Ideal.Quotient.mk (Ideal.ofList (List.ofFn f)) (g j)) hg
      (fun j ↦ Ideal.Quotient.mk (Ideal.ofList (List.ofFn f)) (x (Fin.natAdd n j))) htail
  exact exists_tail_residual_mem_prefix_ideal f g x hbbar

/-- Helper for Lemma 15.30.11: once an appended first cycle is diagonal on the tail modulo the
prefix ideal, the remaining source-proof step is to trade it for a zero-tail prefix cycle and then
apply the prefix `H_1`-regularity. -/
private theorem presentation_class_zero_of_tail_residual_mem_prefix_ideal {n m : ℕ}
    (f : Fin n → A) (g : Fin m → A) (hf : IsH1RegularSequence f)
    (xCycle : koszulFirstCycles (Fin.append f g) A) (b : A)
    (hbTail :
      ∀ j, xCycle.1 (Fin.natAdd n j) - g j * b ∈ Ideal.ofList (List.ofFn f)) :
    (Submodule.Quotient.mk xCycle : koszulH1Presentation (Fin.append f g) A) = 0 := by
  -- Route correction: the remaining source-faithful step is the textbook boundary adjustment.
  -- TODO: express each tail residual with coefficients of `f`, replace `xCycle` by the equal
  -- class of a zero-tail prefix cycle in `koszulH1Presentation`, and then use `hf` to show that
  -- this prefix cycle is diagonal.
  sorry

/-- Helper for Lemma 15.30.11: every appended first cycle already represents the zero class once
the prefix is `H_1`-regular and the quotient tail is `H_1`-regular. -/
private theorem presentation_class_zero_of_append_cycle {n m : ℕ} (f : Fin n → A)
    (g : Fin m → A) (hf : IsH1RegularSequence f)
    (hg : IsH1RegularSequence (fun j ↦ Ideal.Quotient.mk (Ideal.ofList (List.ofFn f)) (g j)))
    (xCycle : koszulFirstCycles (Fin.append f g) A) :
    (Submodule.Quotient.mk xCycle : koszulH1Presentation (Fin.append f g) A) = 0 := by
  -- First kill the quotient-side tail class, then isolate the single remaining boundary-adjustment
  -- step as a dedicated helper.
  obtain ⟨b, hbTail⟩ :=
    exists_tail_diagonal_lift_of_append_cycle f g hg xCycle.1
      (koszulFirstCycleCondition_of_mem
        (f := Fin.append f g) (N := A) xCycle.2)
  exact presentation_class_zero_of_tail_residual_mem_prefix_ideal f g hf xCycle b hbTail

/- 
Domain triage:
* primary domain: `H₁`-regular finite sequences in commutative algebra and their behavior under
  passage to a quotient by the ideal generated by an initial block;
* sampled owner API:
  `RingTheory.Sequence.IsH1RegularSequence`,
  `RingTheory.Sequence.isH1RegularSequence_iff`,
  `RingTheory.Sequence.IsH1RegularOn.isQuasiRegular`,
  `RingTheory.Sequence.IsQuasiRegular.tail_quotient`,
  `Ideal.ofList`,
  `Ideal.ofList_ofFn_eq_span_range`;
* core/canonical owner abstraction: the finite-family predicate `IsH1RegularSequence`, with the
  canonical quotient-by-prefix owner API organized around `Ideal.ofList (List.ofFn f)`;
* primitive data: the prefix `f` and the tail `g`;
  derived API: the quotient-side `H₁`-regularity statement for the image family of `g` in the
  quotient by the prefix ideal generated by `f`;
* layer: `bridge/view`, since this item keeps the source-facing append statement while reusing the
  chapter's canonical quotient-by-prefix owner abstraction.
-/

-- Owner-level bridge: first state the append criterion for the canonical prefix ideal
-- `Ideal.ofList (List.ofFn f)` used by the quotient-by-prefix regular-sequence API.
private theorem isH1RegularSequence_append_of_quotient_ofList {n m : ℕ} (f : Fin n → A)
    (g : Fin m → A) (hf : IsH1RegularSequence f)
    (hg : IsH1RegularSequence (fun j ↦ Ideal.Quotient.mk (Ideal.ofList (List.ofFn f)) (g j))) :
    IsH1RegularSequence (Fin.append f g) := by
  -- Rewrite the target `H_1`-regularity statement using the concrete quotient presentation.
  have hsub :
      Subsingleton (koszulH1Presentation (Fin.append f g) A) := by
    refine ⟨fun u v ↦ ?_⟩
    have hu : u = 0 := by
      refine Quotient.inductionOn u ?_
      intro xCycle
      exact presentation_class_zero_of_append_cycle f g hf hg xCycle
    have hv : v = 0 := by
      refine Quotient.inductionOn v ?_
      intro xCycle
      exact presentation_class_zero_of_append_cycle f g hf hg xCycle
    rw [hu, hv]
  have hzeroPresentation :
      CategoryTheory.Limits.IsZero
        (ModuleCat.of A (koszulH1Presentation (Fin.append f g) A)) :=
    (ModuleCat.isZero_iff_subsingleton).2 hsub
  -- Transport the vanishing statement back from the quotient presentation to the owner object.
  exact (isH1RegularSequence_iff_isZero_koszulH1_local (Fin.append f g)).2
    ((koszulH1IsoPresentation (Fin.append f g) A).isZero_iff.mpr hzeroPresentation)

-- Proof sketch: prove the owner-level append statement for the canonical prefix ideal
-- `Ideal.ofList (List.ofFn f)`, then rewrite that quotient to the source-facing quotient
-- `A ⧸ Ideal.span (Set.range f)` via `Ideal.ofList_ofFn_eq_span_range`.
/-- Lemma 15.30.11: if `f` is an `H_1`-regular sequence in `A`, and the images of `g` form an
`H_1`-regular sequence in the quotient ring `A ⧸ Ideal.span (Set.range f)`, then the concatenated
sequence `Fin.append f g` is `H_1`-regular in `A`. -/
@[stacks 0668]
theorem isH1RegularSequence_append_of_quotient {n m : ℕ} (f : Fin n → A) (g : Fin m → A)
    (hf : IsH1RegularSequence f)
    (hg : IsH1RegularSequence (fun j ↦ Ideal.Quotient.mk (Ideal.span (Set.range f)) (g j))) :
    IsH1RegularSequence (Fin.append f g) := by
  rw [← Ideal.ofList_ofFn_eq_span_range f] at hg
  exact isH1RegularSequence_append_of_quotient_ofList f g hf hg

end RingTheory.Sequence
