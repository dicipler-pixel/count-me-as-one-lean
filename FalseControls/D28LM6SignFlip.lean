-- FALSE CONTROL (D28 item 2): drops the sign, L = +(M^6)⁻¹; fails at L = -1, M = 1.
import Mathlib
theorem false_LM6_sign : ((-1 : ℚ) * 1 ^ 6 = -1) ↔ ((-1 : ℚ) = (1 ^ 6 : ℚ)⁻¹) := by norm_num
