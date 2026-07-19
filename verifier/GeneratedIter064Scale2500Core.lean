import Mathlib

namespace AtomicClaimCertificates

theorem linearCombinationIffGcdDvd (a b c : ℤ) :
    (∃ x y : ℤ, c = a * x + b * y) ↔ ((Int.gcd a b : ℤ) ∣ c) := by
  constructor
  · rintro ⟨x, y, rfl⟩
    exact Int.dvd_add (dvd_mul_of_dvd_left (Int.gcd_dvd_left a b) x)
      (dvd_mul_of_dvd_left (Int.gcd_dvd_right a b) y)
  · rintro ⟨k, rfl⟩
    refine ⟨Int.gcdA a b * k, Int.gcdB a b * k, ?_⟩
    rw [Int.gcd_eq_gcd_ab]
    ring

theorem scale2500_test_0027_gcd : Nat.gcd 1360 1630 = 10 := by
  norm_num [Nat.gcd]

theorem scale2500_test_0027_step_0 : (1630 : ℤ) = 1 * 1360 + 270 := by
  norm_num

theorem scale2500_test_0027_step_1 : (1360 : ℤ) = 5 * 270 + 10 := by
  norm_num

theorem scale2500_test_0027_step_2 : (270 : ℤ) = 27 * 10 + 0 := by
  norm_num

theorem scale2500_test_0027_divides : ¬ (10 : ℤ) ∣ (179 : ℤ) := by
  norm_num

theorem scale2500_test_0027_conclusion : ¬ (∃ x y : ℤ, (179 : ℤ) = (1360 : ℤ) * x + (1630 : ℤ) * y) := by
  have hgcd : (Int.gcd (1360 : ℤ) (1630 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (1360 : ℤ) (1630 : ℤ) (179 : ℤ)).1 h
  rw [hgcd] at hd
  exact scale2500_test_0027_divides hd

end AtomicClaimCertificates
