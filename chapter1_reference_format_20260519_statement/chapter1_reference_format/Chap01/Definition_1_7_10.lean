import Mathlib
import chapter1_reference_format.Chap01.Definition_1_1_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 1.7.10: a partition of a set `S` is a family of nonempty subsets of `S` that are
pairwise disjoint and whose union is exactly `S`; in this project this notion is expressed by
`Set.IsPartition s P`. -/
recall Set.IsPartition {α : Type u} (s : Set α) (P : Set (Set α)) : Prop
