-- FALSE CONTROL: claims w^2 = -1 in Z[w] (true value: w^2 = w - 1).
import FigureEightAnchors.Eisenstein
open FigureEightAnchors
theorem false_w_sq : Eis.w * Eis.w = -1 := by decide
