-- FALSE CONTROL (D28 item 4): T(3,4) Litherland count at alpha = 1/2 is -6, not -4.
import D28.Algebra
theorem false_lt34_half : D28.lt 3 4 (1 / 2) = -4 := by
  rw [D28.lt34_values.2.2.2.2]; decide
