-- FALSE CONTROL: claims a golden shape ramifies on the L = -1 slice (it ramifies on L = +1).
-- In integers mod 11, z = 4 is a golden root; A(-1, 4) = 1 there, not 0.
import FigureEightAnchors.APoly
open FigureEightAnchors.APoly
theorem golden_root_mod11' : (4 : Fin 11) * 4 - 4 - 1 = 0 := by decide
theorem false_golden_minus : A (-1) (4 : Fin 11) = 0 := by decide
