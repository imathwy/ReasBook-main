import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1

open scoped TopCat Topology Topology.Homotopy

noncomputable section

universe u

-- Semantic recall: `lean_leansearch` points to the canonical homotopy-group owner `π_ q`,
-- while this file uses the Chapter 9 induced-map and `IsNEquivalence` API directly for the
-- Postnikov-system conditions.

variable {X : Type u} [TopologicalSpace X]

/-- Definition 22.4.1: a Postnikov system for a simple space `X` records the stage objects,
comparison maps, and homotopy-group conditions appearing in the source definition. -/
structure PostnikovSystem (X : Type u) [TopologicalSpace X] where
  /-- The `n`th stage `Xₙ` of the Postnikov tower. -/
  stage : ℕ → TopCat.{u}
  /-- The comparison map from `X` to the `n`th stage `Xₙ`. -/
  toStage (n : ℕ) : C(X, stage n)
  /-- The bonding map from the `(n + 1)`st stage to the `n`th stage. -/
  bonding (n : ℕ) : C(stage (n + 1), stage n)
  /-- The comparison maps from `X` are compatible with the tower bonding maps. -/
  bonding_comp_toStage (n : ℕ) : (bonding n).comp (toStage (n + 1)) = toStage n
  /-- In every degree `q ≤ n`, the stage map `X ⟶ Xₙ` identifies the `q`th homotopy group of
  `X` with that of `Xₙ`, based at the image of the chosen basepoint. -/
  lowPi_bijective (n q : ℕ) (x : X) (hq : q ≤ n) :
    Function.Bijective ((toStage n).eStar q x)
  /-- In every degree `q > n`, the `n`th stage has trivial `q`th homotopy group at each
  basepoint. -/
  highPi_subsingleton (n q : ℕ) (x : stage n) (hq : n < q) :
    Subsingleton (π_ q (stage n) x)

/-- In a Postnikov system, the stage map `X ⟶ Xₙ` has bijective induced map on `π_q` whenever
`q ≤ n`. -/
theorem PostnikovSystem.bijective_eStar (P : PostnikovSystem X) (n q : ℕ)
    (x : X) (hq : q ≤ n) :
    Function.Bijective ((P.toStage n).eStar q x) :=
  P.lowPi_bijective n q x hq

/-- The stage map `X ⟶ Xₙ` in a Postnikov system is canonically an `n`-equivalence. -/
instance instIsNEquivalenceToStage (P : PostnikovSystem X) (n : ℕ) :
    IsNEquivalence n (P.toStage n) where
  injectiveBelow x {q} hq := (P.bijective_eStar n q x (Nat.le_of_lt hq)).1
  surjectiveUpTo x {q} hq := (P.bijective_eStar n q x hq).2

/-- In a Postnikov system, the `n`th stage has trivial `q`th homotopy group whenever `n < q`. -/
theorem PostnikovSystem.subsingleton_pi_of_lt (P : PostnikovSystem X) {n q : ℕ}
    (hq : n < q) (x : P.stage n) :
    Subsingleton (π_ q (P.stage n) x) :=
  P.highPi_subsingleton n q x hq
