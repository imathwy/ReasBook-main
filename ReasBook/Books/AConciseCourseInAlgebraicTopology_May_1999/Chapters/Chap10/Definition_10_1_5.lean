import Mathlib.Topology.CWComplex.Classical.Subcomplex

-- Declarations for this item will be appended below by the statement pipeline.

universe u

-- Semantic recall via `lean_leansearch`: `Topology.CWComplex.Subcomplex` in
-- `Mathlib.Topology.CWComplex.Classical.Subcomplex` is the canonical owner for subcomplexes of a
-- CW complex, with the same file providing the inherited CW-complex instance and union-of-cells
-- API.

/- Definition 10.1.5: a subcomplex of a CW complex `C` is formalized in mathlib by the exported
owner `Topology.CWComplex.Subcomplex C` (implemented by `Topology.RelCWComplex.Subcomplex` in the
absolute case), recording a union of cells of `C` whose underlying subset is closed. In the
current API, such a subcomplex inherits a CW-complex structure through
`Topology.CWComplex.Subcomplex.instCWComplex` once the ambient space is `T2`, and its underlying
set is the union of its selected open cells via `Topology.CWComplex.Subcomplex.union`. -/
#check Topology.CWComplex.Subcomplex

-- Bridge view: the absolute owner is implemented by the relative subcomplex owner.
#check Topology.RelCWComplex.Subcomplex

#check Topology.CWComplex.Subcomplex.union
#check Topology.CWComplex.Subcomplex.instCWComplex
#check Topology.CWComplex.Subcomplex.union_closedCell
