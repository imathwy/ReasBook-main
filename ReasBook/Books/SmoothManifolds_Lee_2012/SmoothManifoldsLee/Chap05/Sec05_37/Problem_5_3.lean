import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_31.Proposition_5_21

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` returned only general embedding owners, while local repo
-- inspection verified that Proposition 5.21 already provides the exact three `IsEmbedding`
-- statements for this problem.
/-
Problem 5-3: this problem asks for the proof of Proposition 5.21, the sufficient conditions under
which an immersed submanifold is embedded. The faithful item-per-file surface is therefore the
canonical recall of the three existing `IsEmbedding` owners from
`Chap05/Sec05_31/Proposition_5_21.lean`, rather than new stronger `IsSmoothEmbedding` theorems.
-/
recall Manifold.ImmersedSubmanifold.isEmbedding_of_codimension_zero

recall Manifold.ImmersedSubmanifold.isEmbedding_of_proper

recall Manifold.ImmersedSubmanifold.isEmbedding_of_compact
