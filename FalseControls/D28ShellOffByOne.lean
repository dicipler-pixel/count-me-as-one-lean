-- FALSE CONTROL (D28 item 8): shell sum off by one shell; the true value at n = 3 is 18.
import Mathlib
theorem false_shell_sum_three : ∑ l ∈ Finset.range 3, 2 * (2 * l + 1) = 2 * 3 ^ 2 + 2 := by decide
