-- FALSE CONTROL (D28 item 3): wrong second factor t^4 + t^2 + 1; at t = 2: 39 vs 7 * 21 = 147.
import Mathlib
theorem false_t34_factor : ((2 : ℤ) ^ 6 - 2 ^ 5 + 2 ^ 3 - 2 + 1) = (2 ^ 2 - 2 + 1) * (2 ^ 4 + 2 ^ 2 + 1) := by decide
