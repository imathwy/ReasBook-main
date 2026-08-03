module

public import Mathlib.Data.Fintype.CardEmbedding

public section

/- Exercise 6.1 (1): The complete list of injections from a three-element set to
a four-element set. -/
#check (Finset.univ : Finset (Fin 3 ↪ Fin 4))

/-- Exercise 6.1 (2): No injection from a three-element set to a four-element set
is bijective. -/
theorem embeddingFinThreeFour_not_bijective (f : Fin 3 ↪ Fin 4) :
    ¬ Function.Bijective f := by
  -- A bijection would force the domain and codomain to have equal cardinality.
  intro hf
  have hcard : Fintype.card (Fin 3) = Fintype.card (Fin 4) :=
    Fintype.card_of_bijective hf
  -- The resulting numerical equality `3 = 4` is impossible.
  simp at hcard

/-- Exercise 6.1 (3): There are `1814400` injections from an eight-element set to
a ten-element set. -/
theorem cardEmbeddingFinEightTen : Fintype.card (Fin 8 ↪ Fin 10) = 1814400 := by
  -- Count embeddings by the descending factorial of the target cardinality.
  rw [Fintype.card_embedding_eq]
  -- Evaluate `10.descFactorial 8 = 10 · 9 · 8 · 7 · 6 · 5 · 4 · 3`.
  decide
