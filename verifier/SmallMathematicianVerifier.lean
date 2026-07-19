import Mathlib

namespace SmallMathematicianVerifier

theorem bootstrap_smoke (a b : ℤ) (ha : Even a) (hb : Even b) : Even (a + b) := by
  exact ha.add hb

end SmallMathematicianVerifier

