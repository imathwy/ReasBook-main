import SmoothManifoldsLee.Chap02.Sec02_08.Proposition_2_5
import SmoothManifoldsLee.Chap02.Sec02_08.Proposition_2_6
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Exercise 2.7, chart criterion: this is exactly the canonical smoothness criterion already
recorded in Proposition 2.5. -/
recall contMDiff_iff

/- Exercise 2.7, locality on the source: this is exactly the canonical local-to-global smoothness
criterion already recorded in Proposition 2.6. -/
recall contMDiff_of_locally_contMDiffOn

/- Exercise 2.7, restriction to subsets: this is exactly the canonical restriction API already
recorded in Proposition 2.6. -/
recall ContMDiff.contMDiffOn
