-- FALSE CONTROL: claims a golden-branch shape is fixed by the shape cycle z -> 1/(1-z).
-- In integers mod 11, z = 4 is a golden root: 4*4 - 4 - 1 = 11 = 0.
-- The cycle gives z (1 - z) = 4 * (-3) = -12 = -1 (mod 11), not 1, so the kernel must refuse this.
import FigureEightAnchors.Gluing
theorem golden_root_mod11 : (4 : Fin 11) * 4 - 4 - 1 = 0 := by decide
theorem false_golden_regular : (4 : Fin 11) * (1 - 4) = 1 := by decide
