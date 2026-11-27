import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

/-!
# Pythagorean theorem: statement A (Noether)

Source (issue TuriMath/pythagorean-theorem#1; Wikipedia lead, Euclid I.47, Freek 100 item 4):
> [The Pythagorean theorem] states that the area of the square whose side is the hypotenuse
> (the side opposite the right angle) is equal to the sum of the areas of the squares on the other
> two sides. The theorem can be written as an equation relating the lengths of the sides a, b and
> the hypotenuse c: a² + b² = c².
-/

namespace TuriMath.PythagoreanTheorem.A

open EuclideanGeometry Real

/-- The Euclidean plane: `EuclideanSpace ℝ (Fin 2)` (the L² metric, not the sup metric of `ℝ × ℝ`). -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- **Pythagorean theorem** (forward direction only).

Mapping from the source quote to the Lean:
* "a triangle" (implicit) — three points `A B C : Plane` in the Euclidean plane.
* non-degenerate triangle (issue note) — `A ≠ B`, `B ≠ C`, `A ≠ C`.
* "the right angle" — `∠ A C B = π / 2`: the unoriented angle at vertex `C` is a right angle.
* "the hypotenuse (the side opposite the right angle)" — side `AB`, opposite `C`; `c = dist A B`.
* "the other two sides" — `a = dist B C`, `b = dist A C`.
* "the area of the square whose side is …" — the square of that length, `x ^ 2`.
* "is equal to the sum of the areas of the squares on the other two sides", "a² + b² = c²" —
  `dist B C ^ 2 + dist A C ^ 2 = dist A B ^ 2`.

Choices: `ℝ` lengths via Mathlib's `dist`; angle is Mathlib's `EuclideanGeometry.angle` (in `[0, π]`);
the converse is not stated (issue note). -/
def Statement : Prop :=
  ∀ A B C : Plane, A ≠ B → B ≠ C → A ≠ C → ∠ A C B = π / 2 →
    dist B C ^ 2 + dist A C ^ 2 = dist A B ^ 2

/-! ## Sanity section
The hypotheses (three distinct points with a right angle at `C`) can all hold at once:
`A = (1,0)`, `B = (0,1)`, `C = (0,0)`. -/

example : ∃ A B C : Plane, A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ ∠ A C B = π / 2 := by
  refine ⟨EuclideanSpace.single 0 1, EuclideanSpace.single 1 1, 0, ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun v : Plane => v 0) h
    simp at this
  · intro h
    have := congrArg (fun v : Plane => v 1) h
    simp at this
  · intro h
    have := congrArg (fun v : Plane => v 0) h
    simp at this
  · rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
    simp [EuclideanSpace.inner_single_left]

end TuriMath.PythagoreanTheorem.A
