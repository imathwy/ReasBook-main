module

public import Mathlib.Topology.Defs.Sequences

/- Definition 28.3. A subsequence of `x : ℕ → X` has the form `x ∘ φ` for a
strictly increasing map `φ : ℕ → ℕ`. A topological space is sequentially compact
if every sequence has a convergent subsequence. -/
#check SeqCompactSpace
#check IsSeqCompact
#check seqCompactSpace_iff
