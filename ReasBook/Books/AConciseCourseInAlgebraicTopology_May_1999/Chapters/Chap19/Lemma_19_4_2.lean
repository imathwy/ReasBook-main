import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Definition_19_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

-- Semantic recall via `lean_leansearch` did not surface a canonical `lim¹` owner for inverse
-- systems of abelian groups in the current environment, so this item reuses the local API from
-- `Definition_19_4_1` rather than introducing a wrapper theorem.

open CategoryTheory

/-
Lemma 19.4.2. For an inverse sequence `S`, the source-facing `lim¹ A_i` is `S.limOne`, with
quotient map `S.limOneπ`. The standard exact sequence
`0 ⟶ S.lim ⟶ ∏ A_i ⟶ ∏ A_i ⟶ S.limOne ⟶ 0`
and its exactness and endpoint companions remain the Chapter 19 owners from
`Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Definition_19_4_1`.
-/

#check (InverseSequence.limOne : InverseSequence.{u} → Ab.{u})

#check (InverseSequence.limOneπ : ∀ S : InverseSequence.{u}, S.sections ⟶ S.limOne)

#check (InverseSequence.kernelShortComplex_exact :
  ∀ S : InverseSequence.{u}, S.kernelShortComplex.Exact)

#check (InverseSequence.quotientShortComplex_exact :
  ∀ S : InverseSequence.{u}, S.quotientShortComplex.Exact)

#check (InverseSequence.limι_mono : ∀ S : InverseSequence.{u}, Mono S.limι)

#check (InverseSequence.limOneπ_surjective :
  ∀ S : InverseSequence.{u}, Function.Surjective S.limOneπ)
