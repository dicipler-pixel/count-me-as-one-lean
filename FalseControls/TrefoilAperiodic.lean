-- FALSE CONTROL: claims the trefoil monodromy cubed is the identity (it is -I; order is 6, not 3).
import FigureEightAnchors.Monodromy
open FigureEightAnchors.Monodromy FigureEightAnchors.Chirality
theorem false_h31_order3 : mul (mul h31 h31) h31 = I2 := by decide
