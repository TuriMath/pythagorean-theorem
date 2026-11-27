import Theorems.PythagoreanTheorem.A
import Theorems.PythagoreanTheorem.B

namespace TuriMath.PythagoreanTheorem

/-- A and B agree: same points (the Euclidean plane), same non-degeneracy hypotheses, same right
angle at `C`, same conclusion `a² + b² = c²`. Each direction applies the other statement. -/
theorem equiv : A.Statement ↔ B.Statement := by
  constructor
  · intro h P Q R hPQ hQR hPR hang
    exact h P Q R hPQ hQR hPR hang
  · intro h P Q R hPQ hQR hPR hang
    exact h P Q R hPQ hQR hPR hang

end TuriMath.PythagoreanTheorem
