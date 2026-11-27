import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

/-!
# Pythagorean theorem: statement B (Gauss)

Source (issue TuriMath/pythagorean-theorem#1, Wikipedia lead; Euclid I.47; Freek 100 #4):
> [The Pythagorean theorem] states that the area of the square whose side is the hypotenuse
> (the side opposite the right angle) is equal to the sum of the areas of the squares on the
> other two sides. The theorem can be written as an equation relating the lengths of the sides
> a, b and the hypotenuse c: a² + b² = c².

Mapping, one line per part of the quote:
* "a triangle"                  ↦ three points `A B C` of the Euclidean plane
                                   `EuclideanSpace ℝ (Fin 2)` (the ℓ² metric, not `ℝ × ℝ`).
* (non-degenerate triangle)     ↦ `A ≠ B`, `B ≠ C`, `A ≠ C` (needed: Mathlib's angle with a zero
                                   vector is π/2).
* "the right angle"             ↦ `EuclideanGeometry.angle A C B = π / 2`: the angle at vertex `C`.
* "the hypotenuse (the side opposite the right angle)", length c ↦ `dist A B`, the side not
                                   touching `C`.
* "the other two sides", lengths a, b ↦ `dist B C` and `dist A C`.
* "area of the square on a side" ↦ the side length squared, `_ ^ 2`.
* "is equal to the sum of …", a² + b² = c² ↦ `dist B C ^ 2 + dist A C ^ 2 = dist A B ^ 2`.
* Only the forward direction (right angle ⇒ equation), per the issue notes; no converse.
-/

namespace TuriMath.PythagoreanTheorem.B

open EuclideanGeometry

/-- In a non-degenerate triangle `ABC` in the Euclidean plane with a right angle at `C`,
`a² + b² = c²` where `a = BC`, `b = AC` and the hypotenuse `c = AB`. -/
def Statement : Prop :=
  ∀ A B C : EuclideanSpace ℝ (Fin 2),
    A ≠ B → B ≠ C → A ≠ C →
    EuclideanGeometry.angle A C B = Real.pi / 2 →
    dist B C ^ 2 + dist A C ^ 2 = dist A B ^ 2

/-! ## Sanity section

The 3-4-5 triangle: `C = (0,0)`, `A = (3,0)`, `B = (0,4)`. All hypotheses hold at once,
so `Statement` is not vacuous. -/

section Sanity

/-- Vertex with the right angle. -/
noncomputable def C₀ : EuclideanSpace ℝ (Fin 2) := !₂[0, 0]
/-- End of the leg of length 3. -/
noncomputable def A₀ : EuclideanSpace ℝ (Fin 2) := !₂[3, 0]
/-- End of the leg of length 4. -/
noncomputable def B₀ : EuclideanSpace ℝ (Fin 2) := !₂[0, 4]

lemma dist_sq_eq (x y : EuclideanSpace ℝ (Fin 2)) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

-- Distances in the example: for the 3-4-5 triangle, a² = 16, b² = 9, c² = 25.
example : dist B₀ C₀ ^ 2 = 16 := by rw [dist_sq_eq]; simp [B₀, C₀]; norm_num
example : dist A₀ C₀ ^ 2 = 9 := by rw [dist_sq_eq]; simp [A₀, C₀]; norm_num
example : dist A₀ B₀ ^ 2 = 25 := by rw [dist_sq_eq]; simp [A₀, B₀]; norm_num

-- Hypotheses: three distinct vertices.
example : A₀ ≠ B₀ := by
  intro h; have := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h; simp [A₀, B₀] at this
example : B₀ ≠ C₀ := by
  intro h; have := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) h; simp [B₀, C₀] at this
example : A₀ ≠ C₀ := by
  intro h; have := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h; simp [A₀, C₀] at this

-- Hypothesis: the angle at C₀ is a right angle (legs (3,0) and (0,4) have dot product 0).
example : EuclideanGeometry.angle A₀ C₀ B₀ = Real.pi / 2 := by
  rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  simp [A₀, B₀, C₀, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]

-- All hypotheses together, and the conclusion 16 + 9 = 25 on this instance.
example : A₀ ≠ B₀ ∧ B₀ ≠ C₀ ∧ A₀ ≠ C₀ ∧ EuclideanGeometry.angle A₀ C₀ B₀ = Real.pi / 2 ∧
    dist B₀ C₀ ^ 2 + dist A₀ C₀ ^ 2 = dist A₀ B₀ ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; have := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h; simp [A₀, B₀] at this
  · intro h; have := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) h; simp [B₀, C₀] at this
  · intro h; have := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h; simp [A₀, C₀] at this
  · rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
    simp [A₀, B₀, C₀, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  · simp only [dist_sq_eq]; simp [A₀, B₀, C₀]; norm_num

-- Second concrete case, 5-12-13 with the right angle at (1,1):
-- legs to (6,1) and (1,13); 25 + 144 = 169.
example : dist (!₂[1, 13] : EuclideanSpace ℝ (Fin 2)) !₂[1, 1] ^ 2
    + dist (!₂[6, 1] : EuclideanSpace ℝ (Fin 2)) !₂[1, 1] ^ 2
    = dist (!₂[6, 1] : EuclideanSpace ℝ (Fin 2)) !₂[1, 13] ^ 2 := by
  simp only [dist_sq_eq]; simp; norm_num

-- Negative check: a 45° corner (legs (1,0),(1,1)) fails the hypothesis,
-- so the angle condition really restricts: inner product 1 ≠ 0.
example : EuclideanGeometry.angle (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) !₂[0, 0] !₂[1, 1]
    ≠ Real.pi / 2 := by
  rw [EuclideanGeometry.angle, ne_eq, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]

end Sanity

end TuriMath.PythagoreanTheorem.B
