-- FALSE CONTROL: claims the trefoil monodromy has trace 3 (it is 1: elliptic, not hyperbolic).
import FigureEightAnchors.Monodromy
open FigureEightAnchors.Monodromy
theorem false_trefoil_hyperbolic : trace h31 = 3 := by decide
