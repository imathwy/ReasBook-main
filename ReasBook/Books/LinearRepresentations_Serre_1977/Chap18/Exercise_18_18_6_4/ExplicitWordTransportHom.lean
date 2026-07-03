import Mathlib
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_6_4.ExplicitWordTransportData

noncomputable section

open scoped MatrixGroups

local notation "A5" => alternatingGroup (Fin 5)

/-- Helper for Exercise 18-18.6-4: package the stored transport matrix as an element of
`SL₂(𝔽₅)`. -/
def alternating_group_fin5_to_sl_lookup (g : A5) : SL(2, ZMod 5) :=
  ⟨alternating_group_fin5_to_sl_matrix_lookup g,
    alternating_group_fin5_to_sl_matrix_lookup_det g⟩

/-- Helper for Exercise 18-18.6-4: evaluate a word in the distinguished projective generators on
the `PSL₂(𝔽₅)` side. -/
def alternating_group_fin5_word_eval_psl :
    List Bool → PSL(2, ZMod 5)
  | [] => 1
  | false :: w => psl_generator_five * alternating_group_fin5_word_eval_psl w
  | true :: w => psl_generator_two * alternating_group_fin5_word_eval_psl w

/-- Helper for Exercise 18-18.6-4: pair each `A₅` element in the explicit table with the word that
produces it. -/
def alternating_group_fin5_lookup_table : List (A5 × List Bool) :=
  List.zip
    (alternating_group_fin5_word_table.map alternating_group_fin5_word_eval_a5)
    alternating_group_fin5_word_table

/-- Helper for Exercise 18-18.6-4: recover the canonical explicit word assigned to an `A₅`
element by the finite lookup table. -/
def alternating_group_fin5_lookup_word (g : A5) : List Bool :=
  (alternating_group_fin5_lookup_table.find? fun p ↦ p.1 = g).map Prod.snd |>.getD []

/-- Helper for Exercise 18-18.6-4: the table-backed lookup word evaluates to the requested `A₅`
element. -/
theorem alternating_group_fin5_lookup_word_spec
    (g : A5) :
    alternating_group_fin5_word_eval_a5 (alternating_group_fin5_lookup_word g) = g := by
  revert g
  decide

/-- Helper for Exercise 18-18.6-4: descend the stored `SL₂(𝔽₅)` lift to the quotient
`PSL₂(𝔽₅)`. -/
def alternating_group_fin5_to_psl_lookup (g : A5) : PSL(2, ZMod 5) :=
  QuotientGroup.mk (alternating_group_fin5_to_sl_lookup g)

/-- Helper for Exercise 18-18.6-4: the direct transport sends the identity of `A₅` to the
identity of `PSL₂(𝔽₅)`. -/
private theorem alternating_group_fin5_to_psl_lookup_transport_facts :
    alternating_group_fin5_to_psl_lookup 1 = 1 ∧
      (∀ g : A5,
        alternating_group_fin5_to_psl_lookup (a5_generator_five * g) =
          psl_generator_five * alternating_group_fin5_to_psl_lookup g) ∧
      (∀ g : A5,
        alternating_group_fin5_to_psl_lookup (a5_generator_two * g) =
          psl_generator_two * alternating_group_fin5_to_psl_lookup g) := by
  native_decide

/-- Helper for Exercise 18-18.6-4: the direct transport sends the identity of `A₅` to the
identity of `PSL₂(𝔽₅)`. -/
theorem alternating_group_fin5_to_psl_lookup_map_one :
    alternating_group_fin5_to_psl_lookup 1 = 1 := by
  exact alternating_group_fin5_to_psl_lookup_transport_facts.1

/-- Helper for Exercise 18-18.6-4: left multiplication by LinearRepresentations_Serre_1977's order-`5` generator is
transported correctly to `PSL₂(𝔽₅)`. -/
theorem alternating_group_fin5_to_psl_lookup_mul_generator_five
    (g : A5) :
    alternating_group_fin5_to_psl_lookup (a5_generator_five * g) =
      psl_generator_five * alternating_group_fin5_to_psl_lookup g := by
  exact alternating_group_fin5_to_psl_lookup_transport_facts.2.1 g

/-- Helper for Exercise 18-18.6-4: left multiplication by LinearRepresentations_Serre_1977's order-`2` generator is
transported correctly to `PSL₂(𝔽₅)`. -/
theorem alternating_group_fin5_to_psl_lookup_mul_generator_two
    (g : A5) :
    alternating_group_fin5_to_psl_lookup (a5_generator_two * g) =
      psl_generator_two * alternating_group_fin5_to_psl_lookup g := by
  exact alternating_group_fin5_to_psl_lookup_transport_facts.2.2 g

/-- Helper for Exercise 18-18.6-4: the direct transport intertwines left multiplication by any
explicit word in LinearRepresentations_Serre_1977's two generators. -/
theorem alternating_group_fin5_to_psl_lookup_word_mul
    (w : List Bool) (g : A5) :
    alternating_group_fin5_to_psl_lookup
        (alternating_group_fin5_word_eval_a5 w * g) =
      alternating_group_fin5_word_eval_psl w *
        alternating_group_fin5_to_psl_lookup g := by
  induction w generalizing g with
  | nil =>
      simp [alternating_group_fin5_word_eval_a5, alternating_group_fin5_word_eval_psl]
  | cons b w ih =>
      cases b with
      | false =>
          calc
            alternating_group_fin5_to_psl_lookup
                (alternating_group_fin5_word_eval_a5 (false :: w) * g) =
              alternating_group_fin5_to_psl_lookup
                (a5_generator_five * (alternating_group_fin5_word_eval_a5 w * g)) := by
                  simp [alternating_group_fin5_word_eval_a5, mul_assoc]
            _ =
              psl_generator_five *
                alternating_group_fin5_to_psl_lookup
                  (alternating_group_fin5_word_eval_a5 w * g) := by
                    simpa using alternating_group_fin5_to_psl_lookup_mul_generator_five
                      (alternating_group_fin5_word_eval_a5 w * g)
            _ =
              psl_generator_five *
                (alternating_group_fin5_word_eval_psl w *
                  alternating_group_fin5_to_psl_lookup g) := by
                    rw [ih]
            _ =
              alternating_group_fin5_word_eval_psl (false :: w) *
                alternating_group_fin5_to_psl_lookup g := by
                    simp [alternating_group_fin5_word_eval_psl, mul_assoc]
      | true =>
          calc
            alternating_group_fin5_to_psl_lookup
                (alternating_group_fin5_word_eval_a5 (true :: w) * g) =
              alternating_group_fin5_to_psl_lookup
                (a5_generator_two * (alternating_group_fin5_word_eval_a5 w * g)) := by
                  simp [alternating_group_fin5_word_eval_a5, mul_assoc]
            _ =
              psl_generator_two *
                alternating_group_fin5_to_psl_lookup
                  (alternating_group_fin5_word_eval_a5 w * g) := by
                    simpa using alternating_group_fin5_to_psl_lookup_mul_generator_two
                      (alternating_group_fin5_word_eval_a5 w * g)
            _ =
              psl_generator_two *
                (alternating_group_fin5_word_eval_psl w *
                  alternating_group_fin5_to_psl_lookup g) := by
                    rw [ih]
            _ =
              alternating_group_fin5_word_eval_psl (true :: w) *
                alternating_group_fin5_to_psl_lookup g := by
                    simp [alternating_group_fin5_word_eval_psl, mul_assoc]

/-- Helper for Exercise 18-18.6-4: the canonical lookup word and the stored finite transport table
produce the same element of `PSL₂(𝔽₅)`. -/
theorem alternating_group_fin5_to_psl_lookup_eq_word_eval_lookup_word
    (g : A5) :
    alternating_group_fin5_to_psl_lookup g =
      alternating_group_fin5_word_eval_psl (alternating_group_fin5_lookup_word g) := by
  simpa [alternating_group_fin5_lookup_word_spec g, alternating_group_fin5_to_psl_lookup_map_one]
    using alternating_group_fin5_to_psl_lookup_word_mul (alternating_group_fin5_lookup_word g) 1

/-- Helper for Exercise 18-18.6-4: the table-backed direct transport respects multiplication, so
it is a group homomorphism. -/
theorem alternating_group_fin5_to_psl_lookup_map_mul
    (g h : A5) :
    alternating_group_fin5_to_psl_lookup (g * h) =
      alternating_group_fin5_to_psl_lookup g *
        alternating_group_fin5_to_psl_lookup h := by
  calc
    alternating_group_fin5_to_psl_lookup (g * h) =
      alternating_group_fin5_to_psl_lookup
        (alternating_group_fin5_word_eval_a5 (alternating_group_fin5_lookup_word g) * h) := by
          rw [alternating_group_fin5_lookup_word_spec g]
    _ =
      alternating_group_fin5_word_eval_psl (alternating_group_fin5_lookup_word g) *
        alternating_group_fin5_to_psl_lookup h := by
          simpa using alternating_group_fin5_to_psl_lookup_word_mul
            (alternating_group_fin5_lookup_word g) h
    _ =
      alternating_group_fin5_to_psl_lookup g *
        alternating_group_fin5_to_psl_lookup h := by
          rw [alternating_group_fin5_to_psl_lookup_eq_word_eval_lookup_word g]

/-- Helper for Exercise 18-18.6-4: package the finite transport as a monoid homomorphism from
`A₅` to `PSL₂(𝔽₅)`. -/
def alternating_group_fin5_to_psl_hom :
    A5 →* PSL(2, ZMod 5) where
  toFun := alternating_group_fin5_to_psl_lookup
  map_one' := alternating_group_fin5_to_psl_lookup_map_one
  map_mul' := alternating_group_fin5_to_psl_lookup_map_mul
