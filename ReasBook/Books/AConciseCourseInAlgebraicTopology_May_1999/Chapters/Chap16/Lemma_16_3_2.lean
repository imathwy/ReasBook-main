import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Construction_16_3_1

open CategoryTheory Simplicial

universe u

variable (X : TopCat.{u})

-- Semantic recall via `lean_leansearch`: `SSet.S.toN_eq_iff` and `SSet.S.subcomplex_toN` are the
-- canonical owners for the textbook statement that `lambda ∘ rho` sends a simplex to the unique
-- nondegenerate simplex generating the same subcomplex.

/- Lemma 16.3.2. For a simplex `σ` of the singular simplicial set `TopCat.toSSet.obj X`, the
composite `lambda ∘ rho` from Construction 16.3.1 is formalized by `σ.toN`; it is the unique
nondegenerate simplex equivalent to `σ`, where equivalence means generating the same subcomplex.
This is the canonical recall of `SSet.S.toN_eq_iff` together with `SSet.S.subcomplex_toN`,
specialized to `TopCat.toSSet.obj X`. -/
recall SSet.S.toN_eq_iff {X : SSet} {x : X.S} {y : X.N} :
    x.toN = y ↔ y.subcomplex = x.subcomplex

recall SSet.S.subcomplex_toN {X : SSet} (x : X.S) :
    x.toN.subcomplex = x.subcomplex

#check (SSet.S.toN_eq_iff :
    ∀ {σ : (TopCat.toSSet.obj X).S} {τ : (TopCat.toSSet.obj X).N},
      σ.toN = τ ↔ τ.subcomplex = σ.subcomplex)
#check (SSet.S.subcomplex_toN :
    ∀ σ : (TopCat.toSSet.obj X).S, σ.toN.subcomplex = σ.subcomplex)
