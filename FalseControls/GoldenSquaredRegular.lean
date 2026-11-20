-- FALSE CONTROL: claims the golden branch squared lands on the REGULAR polynomial w^2 - w + 1.
-- In integers mod 11, z = 4 is a golden root; w = 16 = 5 and 5*5 - 5 + 1 = 21 = 10, not 0.
import FigureEightAnchors.Ladder
theorem false_golden_sq_regular : (4 * 4 : Fin 11) * (4 * 4) - 4 * 4 + 1 = 0 := by decide
