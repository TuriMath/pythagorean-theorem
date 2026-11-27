import Theorems.PythagoreanTheorem.A

namespace TuriMath.PythagoreanTheorem

open EuclideanGeometry Real

/-- Pythagorean theorem, proved by expanding `‖(A - C) - (B - C)‖²` with the right angle
giving a vanishing inner product (not by citing Mathlib's Pythagoras for angles). -/
theorem main : A.Statement := by
  intro P Q R _ _ _ h
  have hin : inner ℝ (P -ᵥ R) (Q -ᵥ R) = 0 := by
    rw [EuclideanGeometry.angle] at h
    exact InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _ |>.mpr h
  have hPQ : P - Q = (P - R) - (Q - R) := by abel
  rw [vsub_eq_sub, vsub_eq_sub] at hin
  have key : ‖P - Q‖ ^ 2 = ‖P - R‖ ^ 2 + ‖Q - R‖ ^ 2 := by
    rw [hPQ, norm_sub_sq_real, hin]; ring
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, key]; ring

end TuriMath.PythagoreanTheorem
