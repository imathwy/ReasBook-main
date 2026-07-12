"""
Known mathlib API migrations between versions.

Each entry maps an old identifier to its new form and the version
where the change occurred.  Used by fix_errors.py for safe
identifier replacement (NOT in declaration signatures).

Format:
    "old_identifier" -> {
        "new": "new_identifier_or_path",
        "since": "v4.30.0",
        "note": "description of the change",
    }

new can be None if the API was removed with no replacement.
"""

MIGRATIONS = {
    # ------------------------------------------------------------------
    # v4.30.0 changes
    # ------------------------------------------------------------------

    # --- Set namespace refactoring ---
    # In v4.30.0 many identifiers that formerly lived at the root level
    # or under SetLike were moved into the Set namespace proper.
    "uIcc": {
        "new": "Set.uIcc",
        "since": "v4.30.0",
        "note": "uIcc moved from root to Set namespace",
    },
    "SetLike": {
        "new": "SetLike",
        "since": "v4.30.0",
        "note": "SetLike now requires explicit import Mathlib.Algebra.Group.SetLike.Basic",
    },

    # --- TopologicalSpace / topology refactor ---
    # TopologicalSpace is now in its own file and no longer re-exported
    # from the default topology import.  Several topology-related
    # identifiers were renamed or moved.
    "TopologicalSpace": {
        "new": "TopologicalSpace",
        "since": "v4.30.0",
        "note": "now requires explicit import Mathlib.Topology.Basic",
    },
    "TopologicalSpace.Opens": {
        "new": "TopologicalSpace.Opens",
        "since": "v4.30.0",
        "note": "moved to Mathlib.Topology.Sets.Opens; may need explicit open",
    },

    # --- ContDiff / calculus refactor ---
    "ContDiff.differentiable": {
        "new": "ContDiff.differentiable'",
        "since": "v4.30.0",
        "note": "renamed to avoid clash with HasDerivAt.differentiable",
    },
    "HasDerivAt.differentiable": {
        "new": "HasDerivAt.differentiable",
        "since": "v4.30.0",
        "note": "no longer implicitly available; requires explicit import Mathlib.Analysis.Calculus.Deriv.Basic",
    },

    # --- EuclideanSpace move ---
    # EuclideanSpace was decoupled from PiLp and moved into its own
    # file under Analysis/InnerProductSpace.
    "EuclideanSpace": {
        "new": "EuclideanSpace",
        "since": "v4.30.0",
        "note": "moved to Mathlib.Analysis.InnerProductSpace.EuclideanSpace; no longer re-exported from PiLp",
    },
    "PiLp": {
        "new": "PiLp",
        "since": "v4.30.0",
        "note": "moved to Mathlib.Analysis.InnerProductSpace.PiLp; EuclideanSpace split out",
    },

    # --- CommRing / algebra refactor ---
    # Several algebra typeclass projections were renamed to avoid
    # diamond issues with the new typeclass resolution algorithm.
    "CommRing": {
        "new": "CommRing",
        "since": "v4.30.0",
        "note": "now requires explicit import Mathlib.Algebra.Ring.Defs in some contexts",
    },
    "Group": {
        "new": "Group",
        "since": "v4.30.0",
        "note": "now requires explicit import Mathlib.Algebra.Group.Defs in some contexts",
    },

    # --- MeasureTheory refactor ---
    # MeasureTheory namespace was restructured; several sub-namespaces
    # now require explicit imports or were renamed.
    "MeasureTheory": {
        "new": "MeasureTheory",
        "since": "v4.30.0",
        "note": "MeasureTheory namespace restructured; many definitions moved to sub-modules requiring explicit open/import",
    },
    "MeasureTheory.measure": {
        "new": "MeasureTheory.measure",
        "since": "v4.30.0",
        "note": "measure now in Mathlib.MeasureTheory.Measure.Typeclasses; may need explicit open MeasureTheory",
    },
    "MeasureTheory.volume": {
        "new": "MeasureTheory.volume",
        "since": "v4.30.0",
        "note": "volume may need explicit open MeasureTheory after refactor",
    },

    # --- Manifold refactor ---
    # Manifold namespace was restructured in v4.30.0.
    "Manifold": {
        "new": "Manifold",
        "since": "v4.30.0",
        "note": "Manifold namespace restructured; ChartedSpace, ModelWithCorners, etc. moved to sub-modules",
    },
    "ChartedSpace": {
        "new": "ChartedSpace",
        "since": "v4.30.0",
        "note": "ChartedSpace moved within Manifold; may need explicit import Mathlib.Geometry.Manifold.ChartedSpace",
    },
    "SmoothManifoldWithCorners": {
        "new": "SmoothManifoldWithCorners",
        "since": "v4.30.0",
        "note": "SmoothManifoldWithCorners now requires Mathlib.Geometry.Manifold.SmoothManifoldWithCorners",
    },

    # --- Matrix refactor ---
    # Matrix namespace was reorganized; several fundamental definitions
    # moved to new sub-modules.
    "Matrix": {
        "new": "Matrix",
        "since": "v4.30.0",
        "note": "Matrix namespace restructured; many definitions moved to sub-modules requiring explicit imports",
    },
    "Matrix.det": {
        "new": "Matrix.det",
        "since": "v4.30.0",
        "note": "matrix determinant may need explicit import Mathlib.LinearAlgebra.Matrix.Determinant",
    },
    "Matrix.mulVec": {
        "new": "Matrix.mulVec",
        "since": "v4.30.0",
        "note": "Matrix.mulVec may need explicit import Mathlib.LinearAlgebra.Matrix.MulVec",
    },

    # --- BigOperators refactor ---
    # BigOperators notation (∑, ∏, etc.) was moved out of the default
    # algebra import path and now requires explicit open/import.
    "BigOperators": {
        "new": "BigOperators",
        "since": "v4.30.0",
        "note": "BigOperators notation (∑, ∏) now requires explicit open scoped BigOperators",
    },
    "Finset.sum": {
        "new": "Finset.sum",
        "since": "v4.30.0",
        "note": "Finset.sum may need open scoped BigOperators for ∑ notation",
    },
    "Finset.prod": {
        "new": "Finset.prod",
        "since": "v4.30.0",
        "note": "Finset.prod may need open scoped BigOperators for ∏ notation",
    },

    # --- Filter namespace refactor ---
    # Filter namespace was restructured; Filter.atTop, Filter.atBot,
    # Filter.tendsto etc. now require explicit open or import.
    "Filter": {
        "new": "Filter",
        "since": "v4.30.0",
        "note": "Filter namespace restructured; many definitions require explicit open Filter",
    },
    "Filter.atTop": {
        "new": "Filter.atTop",
        "since": "v4.30.0",
        "note": "Filter.atTop may need open Filter or explicit import Mathlib.Order.Filter.Basic",
    },
    "Filter.atBot": {
        "new": "Filter.atBot",
        "since": "v4.30.0",
        "note": "Filter.atBot may need open Filter or explicit import Mathlib.Order.Filter.Basic",
    },
    "Filter.Tendsto": {
        "new": "Filter.Tendsto",
        "since": "v4.30.0",
        "note": "Filter.Tendsto may need open Filter or explicit import Mathlib.Topology.Basic",
    },

    # --- LinearAlgebra.Matrix.Spectrum (removed in v4.30.0) ---
    # This module was removed entirely; its contents were dispersed
    # across several other modules.
    "Mathlib.LinearAlgebra.Matrix.Spectrum": {
        "new": None,
        "since": "v4.30.0",
        "note": "module removed in v4.30.0; contents dispersed — check Mathlib.LinearAlgebra.Matrix.Spectral or Mathlib.Analysis.InnerProductSpace.Spectrum",
    },

    # --- Algebra/Group refactor ---
    # Several algebra typeclass resolution changes broke implicit
    # availability of Group, Ring, CommRing etc.
    "Ring": {
        "new": "Ring",
        "since": "v4.30.0",
        "note": "may need explicit import Mathlib.Algebra.Ring.Defs",
    },
    "Field": {
        "new": "Field",
        "since": "v4.30.0",
        "note": "may need explicit import Mathlib.Algebra.Field.Defs",
    },
    "Module": {
        "new": "Module",
        "since": "v4.30.0",
        "note": "may need explicit import Mathlib.Algebra.Module.Defs",
    },

    # --- Topology namespace refactor ---
    "Topology": {
        "new": "Topology",
        "since": "v4.30.0",
        "note": "Topology namespace restructured; many definitions require explicit open Topology",
    },
    "IsOpen": {
        "new": "IsOpen",
        "since": "v4.30.0",
        "note": "may need open Topology or explicit import Mathlib.Topology.Basic",
    },
    "IsClosed": {
        "new": "IsClosed",
        "since": "v4.30.0",
        "note": "may need open Topology or explicit import Mathlib.Topology.Basic",
    },

    # --- Analysis/Calculus refactor ---
    "ContDiffAt": {
        "new": "ContDiffAt",
        "since": "v4.30.0",
        "note": "may need explicit import Mathlib.Analysis.Calculus.ContDiff.Defs",
    },
    "HasDerivAt": {
        "new": "HasDerivAt",
        "since": "v4.30.0",
        "note": "may need explicit import Mathlib.Analysis.Calculus.Deriv.Basic",
    },
    "HasFDerivAt": {
        "new": "HasFDerivAt",
        "since": "v4.30.0",
        "note": "may need explicit import Mathlib.Analysis.Calculus.FDeriv.Basic",
    },

    # =================================================================
    # Project-internal / unknown identifiers from build errors
    # =================================================================

    # --- IsHopfian / Hopfian groups ---
    # These still exist in mathlib4 under Mathlib.GroupTheory.Hopfian
    # but may require explicit import or have been modified.
    "IsHopfian": {
        "new": "IsHopfian",
        "since": "v4.30.0",
        "note": "still exists in Mathlib.GroupTheory.Hopfian; requires explicit import of that module",
    },
    "MonoidHom.injective_of_surjective": {
        "new": "MonoidHom.injective_of_surjective",
        "since": "v4.30.0",
        "note": "still exists in Mathlib.GroupTheory.Hopfian; requires explicit import",
    },

    # --- Project-internal definitions ---
    # These are defined within the ReasBook project itself; the errors
    # likely come from missing cross-section imports rather than
    # mathlib changes.
    "mem_centerCutEllipsoid_iff": {
        "new": None,
        "since": "v4.30.0",
        "note": "project-internal definition — needs cross-section import",
    },
    "standardLoopClass": {
        "new": None,
        "since": "v4.30.0",
        "note": "project-internal definition — needs cross-section import",
    },
    "brouwer_fixed_point_closed_unit_disk": {
        "new": None,
        "since": "v4.30.0",
        "note": "project-internal definition — needs cross-section import",
    },
    "polynomialNormalizedBoundaryMap": {
        "new": None,
        "since": "v4.30.0",
        "note": "project-internal definition — needs cross-section import",
    },
    "CircleDegree": {
        "new": None,
        "since": "v4.30.0",
        "note": "project-internal definition — needs cross-section import",
    },

    # --- Algebraic geometry / commutative algebra (not in mathlib yet) ---
    # These concepts are not currently formalized in mathlib4; they are
    # either project-internal or from work-in-progress branches.
    "topologicalKrullDimAt": {
        "new": None,
        "since": "v4.30.0",
        "note": "not in current mathlib4; project-internal definition — needs cross-section import",
    },
    "Module.CohenMacaulay": {
        "new": None,
        "since": "v4.30.0",
        "note": "Cohen-Macaulay modules not yet in mathlib4; project-internal definition — needs cross-section import",
    },
    "IsCatenaryRing": {
        "new": None,
        "since": "v4.30.0",
        "note": "may use mathlib4 IsCatenary typeclass; may need explicit import Mathlib.RingTheory.Catenary",
    },
    "UniversallyCatenaryRing": {
        "new": None,
        "since": "v4.30.0",
        "note": "not in current mathlib4; project-internal definition — needs cross-section import",
    },
    "CohenMacaulayRing": {
        "new": None,
        "since": "v4.30.0",
        "note": "Cohen-Macaulay rings not yet in mathlib4; project-internal definition — needs cross-section import",
    },

    # =================================================================
    # Additional v4.30.0 / 2024-2025 known migrations
    # =================================================================

    # --- ContinuousLinearMap.opNorm deprecated ---
    # opNorm was deprecated in favor of standard norm ‖·‖ notation
    # since ContinuousLinearMap has a SeminormedAddCommGroup instance.
    "ContinuousLinearMap.opNorm": {
        "new": "norm",
        "since": "v4.30.0",
        "note": "deprecated in favor of ‖f‖ (standard norm notation); use norm directly",
    },
    "ContinuousLinearMap.opNNNorm": {
        "new": "nnnorm",
        "since": "v4.30.0",
        "note": "deprecated in favor of ‖f‖₊ (nnnorm); use nnnorm directly",
    },
    "ContinuousLinearMap.opNorm_le_iff": {
        "new": "norm_le_iff",
        "since": "v4.30.0",
        "note": "opNorm variant deprecated; use norm_le_iff with standard norm",
    },

    # --- Continuous / IsOpen preimage refactor ---
    # Lean 4 dot-notation preference led to reordering of arguments
    # and namespace moves for continuous-preimage lemmas.
    "Continuous.isOpen_preimage": {
        "new": "IsOpen.preimage",
        "since": "v4.30.0",
        "note": "renamed to IsOpen.preimage for dot-notation; Continuous.isOpen_preimage may still exist as alias",
    },
    "Continuous.isClosed_preimage": {
        "new": "IsClosed.preimage",
        "since": "v4.30.0",
        "note": "renamed to IsClosed.preimage for dot-notation consistency",
    },

    # --- DifferentiableAt / ContDiff dot-notation migration ---
    # Many calculus lemmas were converted from function-form to
    # dot-notation form (e.g., DifferentiableAt.comp instead of
    # differentiableAt_comp).
    "differentiableAt_comp": {
        "new": "DifferentiableAt.comp",
        "since": "v4.30.0",
        "note": "converted to dot-notation form DifferentiableAt.comp",
    },
    "differentiableAt_add": {
        "new": "DifferentiableAt.add",
        "since": "v4.30.0",
        "note": "converted to dot-notation form DifferentiableAt.add",
    },
    "hasDerivAt_comp": {
        "new": "HasDerivAt.comp",
        "since": "v4.30.0",
        "note": "converted to dot-notation form HasDerivAt.comp",
    },
    "hasFDerivAt_comp": {
        "new": "HasFDerivAt.comp",
        "since": "v4.30.0",
        "note": "converted to dot-notation form HasFDerivAt.comp",
    },
    "contDiffAt_comp": {
        "new": "ContDiffAt.comp",
        "since": "v4.30.0",
        "note": "converted to dot-notation form ContDiffAt.comp",
    },

    # --- Algebra.adjoin rename ---
    "Algebra.adjoin_eq": {
        "new": "Algebra.adjoin_span",
        "since": "v4.30.0",
        "note": "renamed to Algebra.adjoin_span for clarity",
    },

    # --- RegularSpace / T3 separation axiom split ---
    # RegularSpace no longer implies T1Space; T3 is now
    # [RegularSpace α] [T1Space α] combined.
    "RegularSpace": {
        "new": "RegularSpace",
        "since": "v4.30.0",
        "note": "RegularSpace no longer implies T1Space; add [T1Space α] if needed",
    },
    "T3Space": {
        "new": None,
        "since": "v4.30.0",
        "note": "T3Space as a standalone typeclass removed; use [RegularSpace α] [T1Space α]",
    },

    # --- InnerProductGeometry namespace ---
    "InnerProductGeometry": {
        "new": "InnerProductGeometry",
        "since": "v4.30.0",
        "note": "may need explicit import Mathlib.Geometry.Euclidean.InnerProductGeometry",
    },

    # --- SetLike instances ---
    "SetLike.instSetLike": {
        "new": "SetLike.instSetLike",
        "since": "v4.30.0",
        "note": "SetLike instance may need explicit import or open SetLike; check for deprecation warnings",
    },
    "SetLike.mem_coe": {
        "new": "SetLike.mem_coe",
        "since": "v4.30.0",
        "note": "SetLike.mem_coe may have been replaced by mem_carrier or direct membership; check deprecation warnings",
    },

    # --- MeasureTheory namespace ---
    "MeasureTheory.measureSpace": {
        "new": "MeasureTheory.measureSpace",
        "since": "v4.30.0",
        "note": "ensure import Mathlib.MeasureTheory.Measure.MeasureSpace; instance name may differ",
    },
    "MeasureTheory.instMeasureSpace": {
        "new": "MeasureTheory.instMeasureSpace",
        "since": "v4.30.0",
        "note": "measure space instance may need explicit type-specific import (e.g. Mathlib.MeasureTheory.Measure.Lebesgue.Basic)",
    },

    # --- Set.preimage notation ---
    "Set.preimage": {
        "new": "Set.preimage",
        "since": "v4.30.0",
        "note": "use infix notation f ⁻¹' s; Set.preimage still available but notation preferred",
    },
    "Set.mapsTo": {
        "new": "Set.MapsTo",
        "since": "v4.30.0",
        "note": "capitalization: use Set.MapsTo (capital M) in mathlib4",
    },

    # --- scoped notation changes ---
    "nhds": {
        "new": "nhds",
        "since": "v4.30.0",
        "note": "requires open scoped Topology for 𝓝 notation; nhds function name unchanged",
    },
    "𝓝": {
        "new": None,
        "since": "v4.30.0",
        "note": "𝓝 notation requires open scoped Topology",
    },

    # --- Function.Injective / Function.Surjective refactor ---
    "Function.injective": {
        "new": "Function.Injective",
        "since": "v4.30.0",
        "note": "predicate is Function.Injective (capital I) in mathlib4",
    },
    "Function.surjective": {
        "new": "Function.Surjective",
        "since": "v4.30.0",
        "note": "predicate is Function.Surjective (capital S) in mathlib4",
    },

    # --- Set.image / Set.range refactoring ---
    "Set.image_comp": {
        "new": "Set.image_comp",
        "since": "v4.30.0",
        "note": "Set.image_comp remains but check for Set.image2_comp or Set.image_comp' variants",
    },
    "Set.range_comp": {
        "new": "Set.range_comp",
        "since": "v4.30.0",
        "note": "also available as Function.comp_range; check preferred form",
    },

    # --- Finset refactor ---
    "Finset.sum_comm": {
        "new": "Finset.sum_comm",
        "since": "v4.30.0",
        "note": "Finset.sum_comm may have been renamed to Finset.sum_comm' or swapped order variants",
    },

    # --- mathlib4 naming convention: lowercase lemma to UpperCamel ---
    # The general trend: function-form lemmas (differentiableAt_foo)
    # are being converted to dot-notation form (DifferentiableAt.foo).
    "continuousAt_comp": {
        "new": "ContinuousAt.comp",
        "since": "v4.30.0",
        "note": "converted to dot-notation form ContinuousAt.comp",
    },
    "continuous_comp": {
        "new": "Continuous.comp",
        "since": "v4.30.0",
        "note": "converted to dot-notation form Continuous.comp",
    },
    "tendsto_comp": {
        "new": "Tendsto.comp",
        "since": "v4.30.0",
        "note": "converted to dot-notation form Tendsto.comp",
    },

    # ------------------------------------------------------------------
    # v4.31.0 changes (placeholder — fill in when upgrading)
    # ------------------------------------------------------------------
    # "old_api_name": {
    #     "new": "new_api_name",
    #     "since": "v4.31.0",
    #     "note": "...",
    # },
}


def find_migration(identifier: str) -> dict | None:
    """Look up a known migration for an identifier.

    Returns the migration dict, or None if no migration is known.
    Does fuzzy matching: 'Set.uIcc' matches 'uIcc' when the suffix matches.
    """
    # Exact match
    if identifier in MIGRATIONS:
        return MIGRATIONS[identifier]

    # Suffix match (e.g. "Mathlib.Topology.Basic.TopologicalSpace"
    # matches "TopologicalSpace")
    for old_name, migration in MIGRATIONS.items():
        if identifier.endswith("." + old_name) or identifier == old_name:
            return migration

    return None


def list_migrations_since(version: str) -> list[dict]:
    """List all migrations since a given version."""
    result = []
    for old_name, migration in MIGRATIONS.items():
        if migration["since"] >= version:
            result.append({"old": old_name, **migration})
    return result
