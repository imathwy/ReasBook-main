module

public import Topology_Munkres_2000.Book.Definition_66_1.WindingNumber
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

public section

/- Lemma 66.3: The source assumes a piecewise-differentiable complex loop, but the
supplied text does not define that regularity convention and no matching project or
mathlib predicate is available. The canonical owners needed by the eventual bridge are: -/
#check PlaneLoop.windingNumber
#check CurveIntegrable
#check curveIntegral
