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

theorem v6medium_test_0002_gcd : Nat.gcd 660 412 = 4 := by
  norm_num [Nat.gcd]

theorem v6medium_test_0002_step_0 : (660 : ℤ) = 1 * 412 + 248 := by
  norm_num

theorem v6medium_test_0002_step_1 : (412 : ℤ) = 1 * 248 + 164 := by
  norm_num

theorem v6medium_test_0002_step_2 : (248 : ℤ) = 1 * 164 + 84 := by
  norm_num

theorem v6medium_test_0002_step_3 : (164 : ℤ) = 1 * 84 + 80 := by
  norm_num

theorem v6medium_test_0002_step_4 : (84 : ℤ) = 1 * 80 + 4 := by
  norm_num

theorem v6medium_test_0002_step_5 : (80 : ℤ) = 20 * 4 + 0 := by
  norm_num

theorem v6medium_test_0002_divides : (4 : ℤ) ∣ (68 : ℤ) := by
  norm_num

theorem v6medium_test_0002_conclusion : ∃ x y : ℤ, (68 : ℤ) = (660 : ℤ) * x + (412 : ℤ) * y := by
  have hgcd : (Int.gcd (660 : ℤ) (412 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (660 : ℤ) (412 : ℤ) (68 : ℤ)).2
  simpa [hgcd] using v6medium_test_0002_divides

theorem v6medium_test_0009_gcd : Nat.gcd 825 726 = 33 := by
  norm_num [Nat.gcd]

theorem v6medium_test_0009_step_0 : (825 : ℤ) = 1 * 726 + 99 := by
  norm_num

theorem v6medium_test_0009_step_1 : (726 : ℤ) = 7 * 99 + 33 := by
  norm_num

theorem v6medium_test_0009_step_2 : (99 : ℤ) = 3 * 33 + 0 := by
  norm_num

theorem v6medium_test_0009_divides : ¬ (33 : ℤ) ∣ (337 : ℤ) := by
  norm_num

theorem v6medium_test_0009_conclusion : ¬ (∃ x y : ℤ, (337 : ℤ) = (825 : ℤ) * x + (726 : ℤ) * y) := by
  have hgcd : (Int.gcd (825 : ℤ) (726 : ℤ) : ℤ) = 33 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (825 : ℤ) (726 : ℤ) (337 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6medium_test_0009_divides hd

theorem v6medium_test_0022_gcd : Nat.gcd 161 266 = 7 := by
  norm_num [Nat.gcd]

theorem v6medium_test_0022_step_0 : (266 : ℤ) = 1 * 161 + 105 := by
  norm_num

theorem v6medium_test_0022_step_1 : (161 : ℤ) = 1 * 105 + 56 := by
  norm_num

theorem v6medium_test_0022_step_2 : (105 : ℤ) = 1 * 56 + 49 := by
  norm_num

theorem v6medium_test_0022_step_3 : (56 : ℤ) = 1 * 49 + 7 := by
  norm_num

theorem v6medium_test_0022_step_4 : (49 : ℤ) = 7 * 7 + 0 := by
  norm_num

theorem v6medium_test_0022_divides : (7 : ℤ) ∣ (91 : ℤ) := by
  norm_num

theorem v6medium_test_0022_conclusion : ∃ x y : ℤ, (91 : ℤ) = (161 : ℤ) * x + (266 : ℤ) * y := by
  have hgcd : (Int.gcd (161 : ℤ) (266 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (161 : ℤ) (266 : ℤ) (91 : ℤ)).2
  simpa [hgcd] using v6medium_test_0022_divides

theorem v6medium_test_0024_gcd : Nat.gcd 462 474 = 6 := by
  norm_num [Nat.gcd]

theorem v6medium_test_0024_step_0 : (474 : ℤ) = 1 * 462 + 12 := by
  norm_num

theorem v6medium_test_0024_step_1 : (462 : ℤ) = 38 * 12 + 6 := by
  norm_num

theorem v6medium_test_0024_step_2 : (12 : ℤ) = 2 * 6 + 0 := by
  norm_num

theorem v6medium_test_0024_divides : (6 : ℤ) ∣ (-102 : ℤ) := by
  norm_num

theorem v6medium_test_0024_conclusion : ∃ x y : ℤ, (-102 : ℤ) = (462 : ℤ) * x + (474 : ℤ) * y := by
  have hgcd : (Int.gcd (462 : ℤ) (474 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (462 : ℤ) (474 : ℤ) (-102 : ℤ)).2
  simpa [hgcd] using v6medium_test_0024_divides

theorem v6medium_test_0025_gcd : Nat.gcd 312 99 = 3 := by
  norm_num [Nat.gcd]

theorem v6medium_test_0025_step_0 : (312 : ℤ) = 3 * 99 + 15 := by
  norm_num

theorem v6medium_test_0025_step_1 : (99 : ℤ) = 6 * 15 + 9 := by
  norm_num

theorem v6medium_test_0025_step_2 : (15 : ℤ) = 1 * 9 + 6 := by
  norm_num

theorem v6medium_test_0025_step_3 : (9 : ℤ) = 1 * 6 + 3 := by
  norm_num

theorem v6medium_test_0025_step_4 : (6 : ℤ) = 2 * 3 + 0 := by
  norm_num

theorem v6medium_test_0025_divides : ¬ (3 : ℤ) ∣ (40 : ℤ) := by
  norm_num

theorem v6medium_test_0025_conclusion : ¬ (∃ x y : ℤ, (40 : ℤ) = (312 : ℤ) * x + (99 : ℤ) * y) := by
  have hgcd : (Int.gcd (312 : ℤ) (99 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (312 : ℤ) (99 : ℤ) (40 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6medium_test_0025_divides hd

theorem v6medium_test_0027_gcd : Nat.gcd 33 408 = 3 := by
  norm_num [Nat.gcd]

theorem v6medium_test_0027_step_0 : (408 : ℤ) = 12 * 33 + 12 := by
  norm_num

theorem v6medium_test_0027_step_1 : (33 : ℤ) = 2 * 12 + 9 := by
  norm_num

theorem v6medium_test_0027_step_2 : (12 : ℤ) = 1 * 9 + 3 := by
  norm_num

theorem v6medium_test_0027_step_3 : (9 : ℤ) = 3 * 3 + 0 := by
  norm_num

theorem v6medium_test_0027_divides : ¬ (3 : ℤ) ∣ (25 : ℤ) := by
  norm_num

theorem v6medium_test_0027_conclusion : ¬ (∃ x y : ℤ, (25 : ℤ) = (33 : ℤ) * x + (408 : ℤ) * y) := by
  have hgcd : (Int.gcd (33 : ℤ) (408 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (33 : ℤ) (408 : ℤ) (25 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6medium_test_0027_divides hd

theorem v6medium_test_0028_gcd : Nat.gcd 888 942 = 6 := by
  norm_num [Nat.gcd]

theorem v6medium_test_0028_step_0 : (942 : ℤ) = 1 * 888 + 54 := by
  norm_num

theorem v6medium_test_0028_step_1 : (888 : ℤ) = 16 * 54 + 24 := by
  norm_num

theorem v6medium_test_0028_step_2 : (54 : ℤ) = 2 * 24 + 6 := by
  norm_num

theorem v6medium_test_0028_step_3 : (24 : ℤ) = 4 * 6 + 0 := by
  norm_num

theorem v6medium_test_0028_divides : (6 : ℤ) ∣ (126 : ℤ) := by
  norm_num

theorem v6medium_test_0028_conclusion : ∃ x y : ℤ, (126 : ℤ) = (888 : ℤ) * x + (942 : ℤ) * y := by
  have hgcd : (Int.gcd (888 : ℤ) (942 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (888 : ℤ) (942 : ℤ) (126 : ℤ)).2
  simpa [hgcd] using v6medium_test_0028_divides

theorem v6medium_test_0032_gcd : Nat.gcd 274 408 = 2 := by
  norm_num [Nat.gcd]

theorem v6medium_test_0032_step_0 : (408 : ℤ) = 1 * 274 + 134 := by
  norm_num

theorem v6medium_test_0032_step_1 : (274 : ℤ) = 2 * 134 + 6 := by
  norm_num

theorem v6medium_test_0032_step_2 : (134 : ℤ) = 22 * 6 + 2 := by
  norm_num

theorem v6medium_test_0032_step_3 : (6 : ℤ) = 3 * 2 + 0 := by
  norm_num

theorem v6medium_test_0032_divides : (2 : ℤ) ∣ (-42 : ℤ) := by
  norm_num

theorem v6medium_test_0032_conclusion : ∃ x y : ℤ, (-42 : ℤ) = (274 : ℤ) * x + (408 : ℤ) * y := by
  have hgcd : (Int.gcd (274 : ℤ) (408 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (274 : ℤ) (408 : ℤ) (-42 : ℤ)).2
  simpa [hgcd] using v6medium_test_0032_divides

theorem v6medium_test_0033_gcd : Nat.gcd 652 684 = 4 := by
  norm_num [Nat.gcd]

theorem v6medium_test_0033_step_0 : (684 : ℤ) = 1 * 652 + 32 := by
  norm_num

theorem v6medium_test_0033_step_1 : (652 : ℤ) = 20 * 32 + 12 := by
  norm_num

theorem v6medium_test_0033_step_2 : (32 : ℤ) = 2 * 12 + 8 := by
  norm_num

theorem v6medium_test_0033_step_3 : (12 : ℤ) = 1 * 8 + 4 := by
  norm_num

theorem v6medium_test_0033_step_4 : (8 : ℤ) = 2 * 4 + 0 := by
  norm_num

theorem v6medium_test_0033_divides : ¬ (4 : ℤ) ∣ (-11 : ℤ) := by
  norm_num

theorem v6medium_test_0033_conclusion : ¬ (∃ x y : ℤ, (-11 : ℤ) = (652 : ℤ) * x + (684 : ℤ) * y) := by
  have hgcd : (Int.gcd (652 : ℤ) (684 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (652 : ℤ) (684 : ℤ) (-11 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6medium_test_0033_divides hd

theorem v6medium_test_0037_gcd : Nat.gcd 590 500 = 10 := by
  norm_num [Nat.gcd]

theorem v6medium_test_0037_step_0 : (590 : ℤ) = 1 * 500 + 90 := by
  norm_num

theorem v6medium_test_0037_step_1 : (500 : ℤ) = 5 * 90 + 50 := by
  norm_num

theorem v6medium_test_0037_step_2 : (90 : ℤ) = 1 * 50 + 40 := by
  norm_num

theorem v6medium_test_0037_step_3 : (50 : ℤ) = 1 * 40 + 10 := by
  norm_num

theorem v6medium_test_0037_step_4 : (40 : ℤ) = 4 * 10 + 0 := by
  norm_num

theorem v6medium_test_0037_divides : ¬ (10 : ℤ) ∣ (-211 : ℤ) := by
  norm_num

theorem v6medium_test_0037_conclusion : ¬ (∃ x y : ℤ, (-211 : ℤ) = (590 : ℤ) * x + (500 : ℤ) * y) := by
  have hgcd : (Int.gcd (590 : ℤ) (500 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (590 : ℤ) (500 : ℤ) (-211 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6medium_test_0037_divides hd

theorem v6medium_test_0038_gcd : Nat.gcd 325 234 = 13 := by
  norm_num [Nat.gcd]

theorem v6medium_test_0038_step_0 : (325 : ℤ) = 1 * 234 + 91 := by
  norm_num

theorem v6medium_test_0038_step_1 : (234 : ℤ) = 2 * 91 + 52 := by
  norm_num

theorem v6medium_test_0038_step_2 : (91 : ℤ) = 1 * 52 + 39 := by
  norm_num

theorem v6medium_test_0038_step_3 : (52 : ℤ) = 1 * 39 + 13 := by
  norm_num

theorem v6medium_test_0038_step_4 : (39 : ℤ) = 3 * 13 + 0 := by
  norm_num

theorem v6medium_test_0038_divides : (13 : ℤ) ∣ (-234 : ℤ) := by
  norm_num

theorem v6medium_test_0038_conclusion : ∃ x y : ℤ, (-234 : ℤ) = (325 : ℤ) * x + (234 : ℤ) * y := by
  have hgcd : (Int.gcd (325 : ℤ) (234 : ℤ) : ℤ) = 13 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (325 : ℤ) (234 : ℤ) (-234 : ℤ)).2
  simpa [hgcd] using v6medium_test_0038_divides

theorem v6medium_test_0042_gcd : Nat.gcd 435 315 = 15 := by
  norm_num [Nat.gcd]

theorem v6medium_test_0042_step_0 : (435 : ℤ) = 1 * 315 + 120 := by
  norm_num

theorem v6medium_test_0042_step_1 : (315 : ℤ) = 2 * 120 + 75 := by
  norm_num

theorem v6medium_test_0042_step_2 : (120 : ℤ) = 1 * 75 + 45 := by
  norm_num

theorem v6medium_test_0042_step_3 : (75 : ℤ) = 1 * 45 + 30 := by
  norm_num

theorem v6medium_test_0042_step_4 : (45 : ℤ) = 1 * 30 + 15 := by
  norm_num

theorem v6medium_test_0042_step_5 : (30 : ℤ) = 2 * 15 + 0 := by
  norm_num

theorem v6medium_test_0042_divides : (15 : ℤ) ∣ (-255 : ℤ) := by
  norm_num

theorem v6medium_test_0042_conclusion : ∃ x y : ℤ, (-255 : ℤ) = (435 : ℤ) * x + (315 : ℤ) * y := by
  have hgcd : (Int.gcd (435 : ℤ) (315 : ℤ) : ℤ) = 15 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (435 : ℤ) (315 : ℤ) (-255 : ℤ)).2
  simpa [hgcd] using v6medium_test_0042_divides

theorem v6medium_test_0048_gcd : Nat.gcd 650 182 = 26 := by
  norm_num [Nat.gcd]

theorem v6medium_test_0048_step_0 : (650 : ℤ) = 3 * 182 + 104 := by
  norm_num

theorem v6medium_test_0048_step_1 : (182 : ℤ) = 1 * 104 + 78 := by
  norm_num

theorem v6medium_test_0048_step_2 : (104 : ℤ) = 1 * 78 + 26 := by
  norm_num

theorem v6medium_test_0048_step_3 : (78 : ℤ) = 3 * 26 + 0 := by
  norm_num

theorem v6medium_test_0048_divides : (26 : ℤ) ∣ (-208 : ℤ) := by
  norm_num

theorem v6medium_test_0048_conclusion : ∃ x y : ℤ, (-208 : ℤ) = (650 : ℤ) * x + (182 : ℤ) * y := by
  have hgcd : (Int.gcd (650 : ℤ) (182 : ℤ) : ℤ) = 26 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (650 : ℤ) (182 : ℤ) (-208 : ℤ)).2
  simpa [hgcd] using v6medium_test_0048_divides

theorem v6medium_test_0051_gcd : Nat.gcd 424 708 = 4 := by
  norm_num [Nat.gcd]

theorem v6medium_test_0051_step_0 : (708 : ℤ) = 1 * 424 + 284 := by
  norm_num

theorem v6medium_test_0051_step_1 : (424 : ℤ) = 1 * 284 + 140 := by
  norm_num

theorem v6medium_test_0051_step_2 : (284 : ℤ) = 2 * 140 + 4 := by
  norm_num

theorem v6medium_test_0051_step_3 : (140 : ℤ) = 35 * 4 + 0 := by
  norm_num

theorem v6medium_test_0051_divides : ¬ (4 : ℤ) ∣ (-57 : ℤ) := by
  norm_num

theorem v6medium_test_0051_conclusion : ¬ (∃ x y : ℤ, (-57 : ℤ) = (424 : ℤ) * x + (708 : ℤ) * y) := by
  have hgcd : (Int.gcd (424 : ℤ) (708 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (424 : ℤ) (708 : ℤ) (-57 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6medium_test_0051_divides hd

theorem v6medium_test_0062_gcd : Nat.gcd 254 140 = 2 := by
  norm_num [Nat.gcd]

theorem v6medium_test_0062_step_0 : (254 : ℤ) = 1 * 140 + 114 := by
  norm_num

theorem v6medium_test_0062_step_1 : (140 : ℤ) = 1 * 114 + 26 := by
  norm_num

theorem v6medium_test_0062_step_2 : (114 : ℤ) = 4 * 26 + 10 := by
  norm_num

theorem v6medium_test_0062_step_3 : (26 : ℤ) = 2 * 10 + 6 := by
  norm_num

theorem v6medium_test_0062_step_4 : (10 : ℤ) = 1 * 6 + 4 := by
  norm_num

theorem v6medium_test_0062_step_5 : (6 : ℤ) = 1 * 4 + 2 := by
  norm_num

theorem v6medium_test_0062_step_6 : (4 : ℤ) = 2 * 2 + 0 := by
  norm_num

theorem v6medium_test_0062_divides : (2 : ℤ) ∣ (-6 : ℤ) := by
  norm_num

theorem v6medium_test_0062_conclusion : ∃ x y : ℤ, (-6 : ℤ) = (254 : ℤ) * x + (140 : ℤ) * y := by
  have hgcd : (Int.gcd (254 : ℤ) (140 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (254 : ℤ) (140 : ℤ) (-6 : ℤ)).2
  simpa [hgcd] using v6medium_test_0062_divides

theorem v6medium_test_0064_gcd : Nat.gcd 231 129 = 3 := by
  norm_num [Nat.gcd]

theorem v6medium_test_0064_step_0 : (231 : ℤ) = 1 * 129 + 102 := by
  norm_num

theorem v6medium_test_0064_step_1 : (129 : ℤ) = 1 * 102 + 27 := by
  norm_num

theorem v6medium_test_0064_step_2 : (102 : ℤ) = 3 * 27 + 21 := by
  norm_num

theorem v6medium_test_0064_step_3 : (27 : ℤ) = 1 * 21 + 6 := by
  norm_num

theorem v6medium_test_0064_step_4 : (21 : ℤ) = 3 * 6 + 3 := by
  norm_num

theorem v6medium_test_0064_step_5 : (6 : ℤ) = 2 * 3 + 0 := by
  norm_num

theorem v6medium_test_0064_divides : (3 : ℤ) ∣ (18 : ℤ) := by
  norm_num

theorem v6medium_test_0064_conclusion : ∃ x y : ℤ, (18 : ℤ) = (231 : ℤ) * x + (129 : ℤ) * y := by
  have hgcd : (Int.gcd (231 : ℤ) (129 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (231 : ℤ) (129 : ℤ) (18 : ℤ)).2
  simpa [hgcd] using v6medium_test_0064_divides

theorem v6medium_test_0065_gcd : Nat.gcd 315 336 = 21 := by
  norm_num [Nat.gcd]

theorem v6medium_test_0065_step_0 : (336 : ℤ) = 1 * 315 + 21 := by
  norm_num

theorem v6medium_test_0065_step_1 : (315 : ℤ) = 15 * 21 + 0 := by
  norm_num

theorem v6medium_test_0065_divides : ¬ (21 : ℤ) ∣ (-16 : ℤ) := by
  norm_num

theorem v6medium_test_0065_conclusion : ¬ (∃ x y : ℤ, (-16 : ℤ) = (315 : ℤ) * x + (336 : ℤ) * y) := by
  have hgcd : (Int.gcd (315 : ℤ) (336 : ℤ) : ℤ) = 21 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (315 : ℤ) (336 : ℤ) (-16 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6medium_test_0065_divides hd

theorem v6medium_test_0079_gcd : Nat.gcd 850 612 = 34 := by
  norm_num [Nat.gcd]

theorem v6medium_test_0079_step_0 : (850 : ℤ) = 1 * 612 + 238 := by
  norm_num

theorem v6medium_test_0079_step_1 : (612 : ℤ) = 2 * 238 + 136 := by
  norm_num

theorem v6medium_test_0079_step_2 : (238 : ℤ) = 1 * 136 + 102 := by
  norm_num

theorem v6medium_test_0079_step_3 : (136 : ℤ) = 1 * 102 + 34 := by
  norm_num

theorem v6medium_test_0079_step_4 : (102 : ℤ) = 3 * 34 + 0 := by
  norm_num

theorem v6medium_test_0079_divides : ¬ (34 : ℤ) ∣ (-206 : ℤ) := by
  norm_num

theorem v6medium_test_0079_conclusion : ¬ (∃ x y : ℤ, (-206 : ℤ) = (850 : ℤ) * x + (612 : ℤ) * y) := by
  have hgcd : (Int.gcd (850 : ℤ) (612 : ℤ) : ℤ) = 34 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (850 : ℤ) (612 : ℤ) (-206 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6medium_test_0079_divides hd

theorem v6medium_test_0088_gcd : Nat.gcd 232 44 = 4 := by
  norm_num [Nat.gcd]

theorem v6medium_test_0088_step_0 : (232 : ℤ) = 5 * 44 + 12 := by
  norm_num

theorem v6medium_test_0088_step_1 : (44 : ℤ) = 3 * 12 + 8 := by
  norm_num

theorem v6medium_test_0088_step_2 : (12 : ℤ) = 1 * 8 + 4 := by
  norm_num

theorem v6medium_test_0088_step_3 : (8 : ℤ) = 2 * 4 + 0 := by
  norm_num

theorem v6medium_test_0088_divides : (4 : ℤ) ∣ (60 : ℤ) := by
  norm_num

theorem v6medium_test_0088_conclusion : ∃ x y : ℤ, (60 : ℤ) = (232 : ℤ) * x + (44 : ℤ) * y := by
  have hgcd : (Int.gcd (232 : ℤ) (44 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (232 : ℤ) (44 : ℤ) (60 : ℤ)).2
  simpa [hgcd] using v6medium_test_0088_divides

theorem v6medium_test_0094_gcd : Nat.gcd 876 120 = 12 := by
  norm_num [Nat.gcd]

theorem v6medium_test_0094_step_0 : (876 : ℤ) = 7 * 120 + 36 := by
  norm_num

theorem v6medium_test_0094_step_1 : (120 : ℤ) = 3 * 36 + 12 := by
  norm_num

theorem v6medium_test_0094_step_2 : (36 : ℤ) = 3 * 12 + 0 := by
  norm_num

theorem v6medium_test_0094_divides : (12 : ℤ) ∣ (-240 : ℤ) := by
  norm_num

theorem v6medium_test_0094_conclusion : ∃ x y : ℤ, (-240 : ℤ) = (876 : ℤ) * x + (120 : ℤ) * y := by
  have hgcd : (Int.gcd (876 : ℤ) (120 : ℤ) : ℤ) = 12 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (876 : ℤ) (120 : ℤ) (-240 : ℤ)).2
  simpa [hgcd] using v6medium_test_0094_divides

theorem v6medium_test_0096_gcd : Nat.gcd 437 703 = 19 := by
  norm_num [Nat.gcd]

theorem v6medium_test_0096_step_0 : (703 : ℤ) = 1 * 437 + 266 := by
  norm_num

theorem v6medium_test_0096_step_1 : (437 : ℤ) = 1 * 266 + 171 := by
  norm_num

theorem v6medium_test_0096_step_2 : (266 : ℤ) = 1 * 171 + 95 := by
  norm_num

theorem v6medium_test_0096_step_3 : (171 : ℤ) = 1 * 95 + 76 := by
  norm_num

theorem v6medium_test_0096_step_4 : (95 : ℤ) = 1 * 76 + 19 := by
  norm_num

theorem v6medium_test_0096_step_5 : (76 : ℤ) = 4 * 19 + 0 := by
  norm_num

theorem v6medium_test_0096_divides : (19 : ℤ) ∣ (-114 : ℤ) := by
  norm_num

theorem v6medium_test_0096_conclusion : ∃ x y : ℤ, (-114 : ℤ) = (437 : ℤ) * x + (703 : ℤ) * y := by
  have hgcd : (Int.gcd (437 : ℤ) (703 : ℤ) : ℤ) = 19 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (437 : ℤ) (703 : ℤ) (-114 : ℤ)).2
  simpa [hgcd] using v6medium_test_0096_divides

theorem v6small_test_0001_gcd : Nat.gcd 55 45 = 5 := by
  norm_num [Nat.gcd]

theorem v6small_test_0001_step_0 : (55 : ℤ) = 1 * 45 + 10 := by
  norm_num

theorem v6small_test_0001_step_1 : (45 : ℤ) = 4 * 10 + 5 := by
  norm_num

theorem v6small_test_0001_step_2 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem v6small_test_0001_divides : ¬ (5 : ℤ) ∣ (-48 : ℤ) := by
  norm_num

theorem v6small_test_0001_conclusion : ¬ (∃ x y : ℤ, (-48 : ℤ) = (55 : ℤ) * x + (45 : ℤ) * y) := by
  have hgcd : (Int.gcd (55 : ℤ) (45 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (55 : ℤ) (45 : ℤ) (-48 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0001_divides hd

theorem v6small_test_0003_gcd : Nat.gcd 18 30 = 6 := by
  norm_num [Nat.gcd]

theorem v6small_test_0003_step_0 : (30 : ℤ) = 1 * 18 + 12 := by
  norm_num

theorem v6small_test_0003_step_1 : (18 : ℤ) = 1 * 12 + 6 := by
  norm_num

theorem v6small_test_0003_step_2 : (12 : ℤ) = 2 * 6 + 0 := by
  norm_num

theorem v6small_test_0003_divides : ¬ (6 : ℤ) ∣ (-7 : ℤ) := by
  norm_num

theorem v6small_test_0003_conclusion : ¬ (∃ x y : ℤ, (-7 : ℤ) = (18 : ℤ) * x + (30 : ℤ) * y) := by
  have hgcd : (Int.gcd (18 : ℤ) (30 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (18 : ℤ) (30 : ℤ) (-7 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0003_divides hd

theorem v6small_test_0004_gcd : Nat.gcd 36 34 = 2 := by
  norm_num [Nat.gcd]

theorem v6small_test_0004_step_0 : (36 : ℤ) = 1 * 34 + 2 := by
  norm_num

theorem v6small_test_0004_step_1 : (34 : ℤ) = 17 * 2 + 0 := by
  norm_num

theorem v6small_test_0004_divides : (2 : ℤ) ∣ (-12 : ℤ) := by
  norm_num

theorem v6small_test_0004_conclusion : ∃ x y : ℤ, (-12 : ℤ) = (36 : ℤ) * x + (34 : ℤ) * y := by
  have hgcd : (Int.gcd (36 : ℤ) (34 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (36 : ℤ) (34 : ℤ) (-12 : ℤ)).2
  simpa [hgcd] using v6small_test_0004_divides

theorem v6small_test_0005_gcd : Nat.gcd 130 150 = 10 := by
  norm_num [Nat.gcd]

theorem v6small_test_0005_step_0 : (150 : ℤ) = 1 * 130 + 20 := by
  norm_num

theorem v6small_test_0005_step_1 : (130 : ℤ) = 6 * 20 + 10 := by
  norm_num

theorem v6small_test_0005_step_2 : (20 : ℤ) = 2 * 10 + 0 := by
  norm_num

theorem v6small_test_0005_divides : ¬ (10 : ℤ) ∣ (124 : ℤ) := by
  norm_num

theorem v6small_test_0005_conclusion : ¬ (∃ x y : ℤ, (124 : ℤ) = (130 : ℤ) * x + (150 : ℤ) * y) := by
  have hgcd : (Int.gcd (130 : ℤ) (150 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (130 : ℤ) (150 : ℤ) (124 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0005_divides hd

theorem v6small_test_0009_gcd : Nat.gcd 42 66 = 6 := by
  norm_num [Nat.gcd]

theorem v6small_test_0009_step_0 : (66 : ℤ) = 1 * 42 + 24 := by
  norm_num

theorem v6small_test_0009_step_1 : (42 : ℤ) = 1 * 24 + 18 := by
  norm_num

theorem v6small_test_0009_step_2 : (24 : ℤ) = 1 * 18 + 6 := by
  norm_num

theorem v6small_test_0009_step_3 : (18 : ℤ) = 3 * 6 + 0 := by
  norm_num

theorem v6small_test_0009_divides : ¬ (6 : ℤ) ∣ (40 : ℤ) := by
  norm_num

theorem v6small_test_0009_conclusion : ¬ (∃ x y : ℤ, (40 : ℤ) = (42 : ℤ) * x + (66 : ℤ) * y) := by
  have hgcd : (Int.gcd (42 : ℤ) (66 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (42 : ℤ) (66 : ℤ) (40 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0009_divides hd

theorem v6small_test_0010_gcd : Nat.gcd 130 20 = 10 := by
  norm_num [Nat.gcd]

theorem v6small_test_0010_step_0 : (130 : ℤ) = 6 * 20 + 10 := by
  norm_num

theorem v6small_test_0010_step_1 : (20 : ℤ) = 2 * 10 + 0 := by
  norm_num

theorem v6small_test_0010_divides : (10 : ℤ) ∣ (110 : ℤ) := by
  norm_num

theorem v6small_test_0010_conclusion : ∃ x y : ℤ, (110 : ℤ) = (130 : ℤ) * x + (20 : ℤ) * y := by
  have hgcd : (Int.gcd (130 : ℤ) (20 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (130 : ℤ) (20 : ℤ) (110 : ℤ)).2
  simpa [hgcd] using v6small_test_0010_divides

theorem v6small_test_0012_gcd : Nat.gcd 20 130 = 10 := by
  norm_num [Nat.gcd]

theorem v6small_test_0012_step_0 : (130 : ℤ) = 6 * 20 + 10 := by
  norm_num

theorem v6small_test_0012_step_1 : (20 : ℤ) = 2 * 10 + 0 := by
  norm_num

theorem v6small_test_0012_divides : (10 : ℤ) ∣ (130 : ℤ) := by
  norm_num

theorem v6small_test_0012_conclusion : ∃ x y : ℤ, (130 : ℤ) = (20 : ℤ) * x + (130 : ℤ) * y := by
  have hgcd : (Int.gcd (20 : ℤ) (130 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (20 : ℤ) (130 : ℤ) (130 : ℤ)).2
  simpa [hgcd] using v6small_test_0012_divides

theorem v6small_test_0014_gcd : Nat.gcd 84 24 = 12 := by
  norm_num [Nat.gcd]

theorem v6small_test_0014_step_0 : (84 : ℤ) = 3 * 24 + 12 := by
  norm_num

theorem v6small_test_0014_step_1 : (24 : ℤ) = 2 * 12 + 0 := by
  norm_num

theorem v6small_test_0014_divides : (12 : ℤ) ∣ (-120 : ℤ) := by
  norm_num

theorem v6small_test_0014_conclusion : ∃ x y : ℤ, (-120 : ℤ) = (84 : ℤ) * x + (24 : ℤ) * y := by
  have hgcd : (Int.gcd (84 : ℤ) (24 : ℤ) : ℤ) = 12 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (84 : ℤ) (24 : ℤ) (-120 : ℤ)).2
  simpa [hgcd] using v6small_test_0014_divides

theorem v6small_test_0017_gcd : Nat.gcd 110 187 = 11 := by
  norm_num [Nat.gcd]

theorem v6small_test_0017_step_0 : (187 : ℤ) = 1 * 110 + 77 := by
  norm_num

theorem v6small_test_0017_step_1 : (110 : ℤ) = 1 * 77 + 33 := by
  norm_num

theorem v6small_test_0017_step_2 : (77 : ℤ) = 2 * 33 + 11 := by
  norm_num

theorem v6small_test_0017_step_3 : (33 : ℤ) = 3 * 11 + 0 := by
  norm_num

theorem v6small_test_0017_divides : ¬ (11 : ℤ) ∣ (-57 : ℤ) := by
  norm_num

theorem v6small_test_0017_conclusion : ¬ (∃ x y : ℤ, (-57 : ℤ) = (110 : ℤ) * x + (187 : ℤ) * y) := by
  have hgcd : (Int.gcd (110 : ℤ) (187 : ℤ) : ℤ) = 11 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (110 : ℤ) (187 : ℤ) (-57 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0017_divides hd

theorem v6small_test_0018_gcd : Nat.gcd 63 91 = 7 := by
  norm_num [Nat.gcd]

theorem v6small_test_0018_step_0 : (91 : ℤ) = 1 * 63 + 28 := by
  norm_num

theorem v6small_test_0018_step_1 : (63 : ℤ) = 2 * 28 + 7 := by
  norm_num

theorem v6small_test_0018_step_2 : (28 : ℤ) = 4 * 7 + 0 := by
  norm_num

theorem v6small_test_0018_divides : (7 : ℤ) ∣ (-98 : ℤ) := by
  norm_num

theorem v6small_test_0018_conclusion : ∃ x y : ℤ, (-98 : ℤ) = (63 : ℤ) * x + (91 : ℤ) * y := by
  have hgcd : (Int.gcd (63 : ℤ) (91 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (63 : ℤ) (91 : ℤ) (-98 : ℤ)).2
  simpa [hgcd] using v6small_test_0018_divides

theorem v6small_test_0019_gcd : Nat.gcd 90 63 = 9 := by
  norm_num [Nat.gcd]

theorem v6small_test_0019_step_0 : (90 : ℤ) = 1 * 63 + 27 := by
  norm_num

theorem v6small_test_0019_step_1 : (63 : ℤ) = 2 * 27 + 9 := by
  norm_num

theorem v6small_test_0019_step_2 : (27 : ℤ) = 3 * 9 + 0 := by
  norm_num

theorem v6small_test_0019_divides : ¬ (9 : ℤ) ∣ (123 : ℤ) := by
  norm_num

theorem v6small_test_0019_conclusion : ¬ (∃ x y : ℤ, (123 : ℤ) = (90 : ℤ) * x + (63 : ℤ) * y) := by
  have hgcd : (Int.gcd (90 : ℤ) (63 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (90 : ℤ) (63 : ℤ) (123 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0019_divides hd

theorem v6small_test_0020_gcd : Nat.gcd 112 120 = 8 := by
  norm_num [Nat.gcd]

theorem v6small_test_0020_step_0 : (120 : ℤ) = 1 * 112 + 8 := by
  norm_num

theorem v6small_test_0020_step_1 : (112 : ℤ) = 14 * 8 + 0 := by
  norm_num

theorem v6small_test_0020_divides : (8 : ℤ) ∣ (-48 : ℤ) := by
  norm_num

theorem v6small_test_0020_conclusion : ∃ x y : ℤ, (-48 : ℤ) = (112 : ℤ) * x + (120 : ℤ) * y := by
  have hgcd : (Int.gcd (112 : ℤ) (120 : ℤ) : ℤ) = 8 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (112 : ℤ) (120 : ℤ) (-48 : ℤ)).2
  simpa [hgcd] using v6small_test_0020_divides

theorem v6small_test_0022_gcd : Nat.gcd 48 20 = 4 := by
  norm_num [Nat.gcd]

theorem v6small_test_0022_step_0 : (48 : ℤ) = 2 * 20 + 8 := by
  norm_num

theorem v6small_test_0022_step_1 : (20 : ℤ) = 2 * 8 + 4 := by
  norm_num

theorem v6small_test_0022_step_2 : (8 : ℤ) = 2 * 4 + 0 := by
  norm_num

theorem v6small_test_0022_divides : (4 : ℤ) ∣ (24 : ℤ) := by
  norm_num

theorem v6small_test_0022_conclusion : ∃ x y : ℤ, (24 : ℤ) = (48 : ℤ) * x + (20 : ℤ) * y := by
  have hgcd : (Int.gcd (48 : ℤ) (20 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (48 : ℤ) (20 : ℤ) (24 : ℤ)).2
  simpa [hgcd] using v6small_test_0022_divides

theorem v6small_test_0023_gcd : Nat.gcd 204 108 = 12 := by
  norm_num [Nat.gcd]

theorem v6small_test_0023_step_0 : (204 : ℤ) = 1 * 108 + 96 := by
  norm_num

theorem v6small_test_0023_step_1 : (108 : ℤ) = 1 * 96 + 12 := by
  norm_num

theorem v6small_test_0023_step_2 : (96 : ℤ) = 8 * 12 + 0 := by
  norm_num

theorem v6small_test_0023_divides : ¬ (12 : ℤ) ∣ (46 : ℤ) := by
  norm_num

theorem v6small_test_0023_conclusion : ¬ (∃ x y : ℤ, (46 : ℤ) = (204 : ℤ) * x + (108 : ℤ) * y) := by
  have hgcd : (Int.gcd (204 : ℤ) (108 : ℤ) : ℤ) = 12 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (204 : ℤ) (108 : ℤ) (46 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0023_divides hd

theorem v6small_test_0024_gcd : Nat.gcd 25 15 = 5 := by
  norm_num [Nat.gcd]

theorem v6small_test_0024_step_0 : (25 : ℤ) = 1 * 15 + 10 := by
  norm_num

theorem v6small_test_0024_step_1 : (15 : ℤ) = 1 * 10 + 5 := by
  norm_num

theorem v6small_test_0024_step_2 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem v6small_test_0024_divides : (5 : ℤ) ∣ (65 : ℤ) := by
  norm_num

theorem v6small_test_0024_conclusion : ∃ x y : ℤ, (65 : ℤ) = (25 : ℤ) * x + (15 : ℤ) * y := by
  have hgcd : (Int.gcd (25 : ℤ) (15 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (25 : ℤ) (15 : ℤ) (65 : ℤ)).2
  simpa [hgcd] using v6small_test_0024_divides

theorem v6small_test_0025_gcd : Nat.gcd 90 130 = 10 := by
  norm_num [Nat.gcd]

theorem v6small_test_0025_step_0 : (130 : ℤ) = 1 * 90 + 40 := by
  norm_num

theorem v6small_test_0025_step_1 : (90 : ℤ) = 2 * 40 + 10 := by
  norm_num

theorem v6small_test_0025_step_2 : (40 : ℤ) = 4 * 10 + 0 := by
  norm_num

theorem v6small_test_0025_divides : ¬ (10 : ℤ) ∣ (-87 : ℤ) := by
  norm_num

theorem v6small_test_0025_conclusion : ¬ (∃ x y : ℤ, (-87 : ℤ) = (90 : ℤ) * x + (130 : ℤ) * y) := by
  have hgcd : (Int.gcd (90 : ℤ) (130 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (90 : ℤ) (130 : ℤ) (-87 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0025_divides hd

theorem v6small_test_0028_gcd : Nat.gcd 21 98 = 7 := by
  norm_num [Nat.gcd]

theorem v6small_test_0028_step_0 : (98 : ℤ) = 4 * 21 + 14 := by
  norm_num

theorem v6small_test_0028_step_1 : (21 : ℤ) = 1 * 14 + 7 := by
  norm_num

theorem v6small_test_0028_step_2 : (14 : ℤ) = 2 * 7 + 0 := by
  norm_num

theorem v6small_test_0028_divides : (7 : ℤ) ∣ (14 : ℤ) := by
  norm_num

theorem v6small_test_0028_conclusion : ∃ x y : ℤ, (14 : ℤ) = (21 : ℤ) * x + (98 : ℤ) * y := by
  have hgcd : (Int.gcd (21 : ℤ) (98 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (21 : ℤ) (98 : ℤ) (14 : ℤ)).2
  simpa [hgcd] using v6small_test_0028_divides

theorem v6small_test_0029_gcd : Nat.gcd 12 39 = 3 := by
  norm_num [Nat.gcd]

theorem v6small_test_0029_step_0 : (39 : ℤ) = 3 * 12 + 3 := by
  norm_num

theorem v6small_test_0029_step_1 : (12 : ℤ) = 4 * 3 + 0 := by
  norm_num

theorem v6small_test_0029_divides : ¬ (3 : ℤ) ∣ (-41 : ℤ) := by
  norm_num

theorem v6small_test_0029_conclusion : ¬ (∃ x y : ℤ, (-41 : ℤ) = (12 : ℤ) * x + (39 : ℤ) * y) := by
  have hgcd : (Int.gcd (12 : ℤ) (39 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (12 : ℤ) (39 : ℤ) (-41 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0029_divides hd

theorem v6small_test_0030_gcd : Nat.gcd 27 18 = 9 := by
  norm_num [Nat.gcd]

theorem v6small_test_0030_step_0 : (27 : ℤ) = 1 * 18 + 9 := by
  norm_num

theorem v6small_test_0030_step_1 : (18 : ℤ) = 2 * 9 + 0 := by
  norm_num

theorem v6small_test_0030_divides : (9 : ℤ) ∣ (108 : ℤ) := by
  norm_num

theorem v6small_test_0030_conclusion : ∃ x y : ℤ, (108 : ℤ) = (27 : ℤ) * x + (18 : ℤ) * y := by
  have hgcd : (Int.gcd (27 : ℤ) (18 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (27 : ℤ) (18 : ℤ) (108 : ℤ)).2
  simpa [hgcd] using v6small_test_0030_divides

theorem v6small_test_0031_gcd : Nat.gcd 45 35 = 5 := by
  norm_num [Nat.gcd]

theorem v6small_test_0031_step_0 : (45 : ℤ) = 1 * 35 + 10 := by
  norm_num

theorem v6small_test_0031_step_1 : (35 : ℤ) = 3 * 10 + 5 := by
  norm_num

theorem v6small_test_0031_step_2 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem v6small_test_0031_divides : ¬ (5 : ℤ) ∣ (-26 : ℤ) := by
  norm_num

theorem v6small_test_0031_conclusion : ¬ (∃ x y : ℤ, (-26 : ℤ) = (45 : ℤ) * x + (35 : ℤ) * y) := by
  have hgcd : (Int.gcd (45 : ℤ) (35 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (45 : ℤ) (35 : ℤ) (-26 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0031_divides hd

theorem v6small_test_0032_gcd : Nat.gcd 90 55 = 5 := by
  norm_num [Nat.gcd]

theorem v6small_test_0032_step_0 : (90 : ℤ) = 1 * 55 + 35 := by
  norm_num

theorem v6small_test_0032_step_1 : (55 : ℤ) = 1 * 35 + 20 := by
  norm_num

theorem v6small_test_0032_step_2 : (35 : ℤ) = 1 * 20 + 15 := by
  norm_num

theorem v6small_test_0032_step_3 : (20 : ℤ) = 1 * 15 + 5 := by
  norm_num

theorem v6small_test_0032_step_4 : (15 : ℤ) = 3 * 5 + 0 := by
  norm_num

theorem v6small_test_0032_divides : (5 : ℤ) ∣ (-5 : ℤ) := by
  norm_num

theorem v6small_test_0032_conclusion : ∃ x y : ℤ, (-5 : ℤ) = (90 : ℤ) * x + (55 : ℤ) * y := by
  have hgcd : (Int.gcd (90 : ℤ) (55 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (90 : ℤ) (55 : ℤ) (-5 : ℤ)).2
  simpa [hgcd] using v6small_test_0032_divides

theorem v6small_test_0033_gcd : Nat.gcd 80 15 = 5 := by
  norm_num [Nat.gcd]

theorem v6small_test_0033_step_0 : (80 : ℤ) = 5 * 15 + 5 := by
  norm_num

theorem v6small_test_0033_step_1 : (15 : ℤ) = 3 * 5 + 0 := by
  norm_num

theorem v6small_test_0033_divides : ¬ (5 : ℤ) ∣ (-63 : ℤ) := by
  norm_num

theorem v6small_test_0033_conclusion : ¬ (∃ x y : ℤ, (-63 : ℤ) = (80 : ℤ) * x + (15 : ℤ) * y) := by
  have hgcd : (Int.gcd (80 : ℤ) (15 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (80 : ℤ) (15 : ℤ) (-63 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0033_divides hd

theorem v6small_test_0034_gcd : Nat.gcd 100 90 = 10 := by
  norm_num [Nat.gcd]

theorem v6small_test_0034_step_0 : (100 : ℤ) = 1 * 90 + 10 := by
  norm_num

theorem v6small_test_0034_step_1 : (90 : ℤ) = 9 * 10 + 0 := by
  norm_num

theorem v6small_test_0034_divides : (10 : ℤ) ∣ (130 : ℤ) := by
  norm_num

theorem v6small_test_0034_conclusion : ∃ x y : ℤ, (130 : ℤ) = (100 : ℤ) * x + (90 : ℤ) * y := by
  have hgcd : (Int.gcd (100 : ℤ) (90 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (100 : ℤ) (90 : ℤ) (130 : ℤ)).2
  simpa [hgcd] using v6small_test_0034_divides

theorem v6small_test_0036_gcd : Nat.gcd 112 119 = 7 := by
  norm_num [Nat.gcd]

theorem v6small_test_0036_step_0 : (119 : ℤ) = 1 * 112 + 7 := by
  norm_num

theorem v6small_test_0036_step_1 : (112 : ℤ) = 16 * 7 + 0 := by
  norm_num

theorem v6small_test_0036_divides : (7 : ℤ) ∣ (84 : ℤ) := by
  norm_num

theorem v6small_test_0036_conclusion : ∃ x y : ℤ, (84 : ℤ) = (112 : ℤ) * x + (119 : ℤ) * y := by
  have hgcd : (Int.gcd (112 : ℤ) (119 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (112 : ℤ) (119 : ℤ) (84 : ℤ)).2
  simpa [hgcd] using v6small_test_0036_divides

theorem v6small_test_0038_gcd : Nat.gcd 22 8 = 2 := by
  norm_num [Nat.gcd]

theorem v6small_test_0038_step_0 : (22 : ℤ) = 2 * 8 + 6 := by
  norm_num

theorem v6small_test_0038_step_1 : (8 : ℤ) = 1 * 6 + 2 := by
  norm_num

theorem v6small_test_0038_step_2 : (6 : ℤ) = 3 * 2 + 0 := by
  norm_num

theorem v6small_test_0038_divides : (2 : ℤ) ∣ (-14 : ℤ) := by
  norm_num

theorem v6small_test_0038_conclusion : ∃ x y : ℤ, (-14 : ℤ) = (22 : ℤ) * x + (8 : ℤ) * y := by
  have hgcd : (Int.gcd (22 : ℤ) (8 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (22 : ℤ) (8 : ℤ) (-14 : ℤ)).2
  simpa [hgcd] using v6small_test_0038_divides

theorem v6small_test_0039_gcd : Nat.gcd 66 121 = 11 := by
  norm_num [Nat.gcd]

theorem v6small_test_0039_step_0 : (121 : ℤ) = 1 * 66 + 55 := by
  norm_num

theorem v6small_test_0039_step_1 : (66 : ℤ) = 1 * 55 + 11 := by
  norm_num

theorem v6small_test_0039_step_2 : (55 : ℤ) = 5 * 11 + 0 := by
  norm_num

theorem v6small_test_0039_divides : ¬ (11 : ℤ) ∣ (-69 : ℤ) := by
  norm_num

theorem v6small_test_0039_conclusion : ¬ (∃ x y : ℤ, (-69 : ℤ) = (66 : ℤ) * x + (121 : ℤ) * y) := by
  have hgcd : (Int.gcd (66 : ℤ) (121 : ℤ) : ℤ) = 11 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (66 : ℤ) (121 : ℤ) (-69 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0039_divides hd

theorem v6small_test_0040_gcd : Nat.gcd 28 49 = 7 := by
  norm_num [Nat.gcd]

theorem v6small_test_0040_step_0 : (49 : ℤ) = 1 * 28 + 21 := by
  norm_num

theorem v6small_test_0040_step_1 : (28 : ℤ) = 1 * 21 + 7 := by
  norm_num

theorem v6small_test_0040_step_2 : (21 : ℤ) = 3 * 7 + 0 := by
  norm_num

theorem v6small_test_0040_divides : (7 : ℤ) ∣ (-49 : ℤ) := by
  norm_num

theorem v6small_test_0040_conclusion : ∃ x y : ℤ, (-49 : ℤ) = (28 : ℤ) * x + (49 : ℤ) * y := by
  have hgcd : (Int.gcd (28 : ℤ) (49 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (28 : ℤ) (49 : ℤ) (-49 : ℤ)).2
  simpa [hgcd] using v6small_test_0040_divides

theorem v6small_test_0042_gcd : Nat.gcd 36 30 = 6 := by
  norm_num [Nat.gcd]

theorem v6small_test_0042_step_0 : (36 : ℤ) = 1 * 30 + 6 := by
  norm_num

theorem v6small_test_0042_step_1 : (30 : ℤ) = 5 * 6 + 0 := by
  norm_num

theorem v6small_test_0042_divides : (6 : ℤ) ∣ (36 : ℤ) := by
  norm_num

theorem v6small_test_0042_conclusion : ∃ x y : ℤ, (36 : ℤ) = (36 : ℤ) * x + (30 : ℤ) * y := by
  have hgcd : (Int.gcd (36 : ℤ) (30 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (36 : ℤ) (30 : ℤ) (36 : ℤ)).2
  simpa [hgcd] using v6small_test_0042_divides

theorem v6small_test_0043_gcd : Nat.gcd 84 35 = 7 := by
  norm_num [Nat.gcd]

theorem v6small_test_0043_step_0 : (84 : ℤ) = 2 * 35 + 14 := by
  norm_num

theorem v6small_test_0043_step_1 : (35 : ℤ) = 2 * 14 + 7 := by
  norm_num

theorem v6small_test_0043_step_2 : (14 : ℤ) = 2 * 7 + 0 := by
  norm_num

theorem v6small_test_0043_divides : ¬ (7 : ℤ) ∣ (106 : ℤ) := by
  norm_num

theorem v6small_test_0043_conclusion : ¬ (∃ x y : ℤ, (106 : ℤ) = (84 : ℤ) * x + (35 : ℤ) * y) := by
  have hgcd : (Int.gcd (84 : ℤ) (35 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (84 : ℤ) (35 : ℤ) (106 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0043_divides hd

theorem v6small_test_0044_gcd : Nat.gcd 25 90 = 5 := by
  norm_num [Nat.gcd]

theorem v6small_test_0044_step_0 : (90 : ℤ) = 3 * 25 + 15 := by
  norm_num

theorem v6small_test_0044_step_1 : (25 : ℤ) = 1 * 15 + 10 := by
  norm_num

theorem v6small_test_0044_step_2 : (15 : ℤ) = 1 * 10 + 5 := by
  norm_num

theorem v6small_test_0044_step_3 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem v6small_test_0044_divides : (5 : ℤ) ∣ (75 : ℤ) := by
  norm_num

theorem v6small_test_0044_conclusion : ∃ x y : ℤ, (75 : ℤ) = (25 : ℤ) * x + (90 : ℤ) * y := by
  have hgcd : (Int.gcd (25 : ℤ) (90 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (25 : ℤ) (90 : ℤ) (75 : ℤ)).2
  simpa [hgcd] using v6small_test_0044_divides

theorem v6small_test_0047_gcd : Nat.gcd 54 30 = 6 := by
  norm_num [Nat.gcd]

theorem v6small_test_0047_step_0 : (54 : ℤ) = 1 * 30 + 24 := by
  norm_num

theorem v6small_test_0047_step_1 : (30 : ℤ) = 1 * 24 + 6 := by
  norm_num

theorem v6small_test_0047_step_2 : (24 : ℤ) = 4 * 6 + 0 := by
  norm_num

theorem v6small_test_0047_divides : ¬ (6 : ℤ) ∣ (69 : ℤ) := by
  norm_num

theorem v6small_test_0047_conclusion : ¬ (∃ x y : ℤ, (69 : ℤ) = (54 : ℤ) * x + (30 : ℤ) * y) := by
  have hgcd : (Int.gcd (54 : ℤ) (30 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (54 : ℤ) (30 : ℤ) (69 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0047_divides hd

theorem v6small_test_0049_gcd : Nat.gcd 24 36 = 12 := by
  norm_num [Nat.gcd]

theorem v6small_test_0049_step_0 : (36 : ℤ) = 1 * 24 + 12 := by
  norm_num

theorem v6small_test_0049_step_1 : (24 : ℤ) = 2 * 12 + 0 := by
  norm_num

theorem v6small_test_0049_divides : ¬ (12 : ℤ) ∣ (160 : ℤ) := by
  norm_num

theorem v6small_test_0049_conclusion : ¬ (∃ x y : ℤ, (160 : ℤ) = (24 : ℤ) * x + (36 : ℤ) * y) := by
  have hgcd : (Int.gcd (24 : ℤ) (36 : ℤ) : ℤ) = 12 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (24 : ℤ) (36 : ℤ) (160 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0049_divides hd

theorem v6small_test_0051_gcd : Nat.gcd 40 15 = 5 := by
  norm_num [Nat.gcd]

theorem v6small_test_0051_step_0 : (40 : ℤ) = 2 * 15 + 10 := by
  norm_num

theorem v6small_test_0051_step_1 : (15 : ℤ) = 1 * 10 + 5 := by
  norm_num

theorem v6small_test_0051_step_2 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem v6small_test_0051_divides : ¬ (5 : ℤ) ∣ (-54 : ℤ) := by
  norm_num

theorem v6small_test_0051_conclusion : ¬ (∃ x y : ℤ, (-54 : ℤ) = (40 : ℤ) * x + (15 : ℤ) * y) := by
  have hgcd : (Int.gcd (40 : ℤ) (15 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (40 : ℤ) (15 : ℤ) (-54 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0051_divides hd

theorem v6small_test_0055_gcd : Nat.gcd 40 15 = 5 := by
  norm_num [Nat.gcd]

theorem v6small_test_0055_step_0 : (40 : ℤ) = 2 * 15 + 10 := by
  norm_num

theorem v6small_test_0055_step_1 : (15 : ℤ) = 1 * 10 + 5 := by
  norm_num

theorem v6small_test_0055_step_2 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem v6small_test_0055_divides : ¬ (5 : ℤ) ∣ (-57 : ℤ) := by
  norm_num

theorem v6small_test_0055_conclusion : ¬ (∃ x y : ℤ, (-57 : ℤ) = (40 : ℤ) * x + (15 : ℤ) * y) := by
  have hgcd : (Int.gcd (40 : ℤ) (15 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (40 : ℤ) (15 : ℤ) (-57 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0055_divides hd

theorem v6small_test_0056_gcd : Nat.gcd 70 30 = 10 := by
  norm_num [Nat.gcd]

theorem v6small_test_0056_step_0 : (70 : ℤ) = 2 * 30 + 10 := by
  norm_num

theorem v6small_test_0056_step_1 : (30 : ℤ) = 3 * 10 + 0 := by
  norm_num

theorem v6small_test_0056_divides : (10 : ℤ) ∣ (150 : ℤ) := by
  norm_num

theorem v6small_test_0056_conclusion : ∃ x y : ℤ, (150 : ℤ) = (70 : ℤ) * x + (30 : ℤ) * y := by
  have hgcd : (Int.gcd (70 : ℤ) (30 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (70 : ℤ) (30 : ℤ) (150 : ℤ)).2
  simpa [hgcd] using v6small_test_0056_divides

theorem v6small_test_0057_gcd : Nat.gcd 28 35 = 7 := by
  norm_num [Nat.gcd]

theorem v6small_test_0057_step_0 : (35 : ℤ) = 1 * 28 + 7 := by
  norm_num

theorem v6small_test_0057_step_1 : (28 : ℤ) = 4 * 7 + 0 := by
  norm_num

theorem v6small_test_0057_divides : ¬ (7 : ℤ) ∣ (-72 : ℤ) := by
  norm_num

theorem v6small_test_0057_conclusion : ¬ (∃ x y : ℤ, (-72 : ℤ) = (28 : ℤ) * x + (35 : ℤ) * y) := by
  have hgcd : (Int.gcd (28 : ℤ) (35 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (28 : ℤ) (35 : ℤ) (-72 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0057_divides hd

theorem v6small_test_0058_gcd : Nat.gcd 15 40 = 5 := by
  norm_num [Nat.gcd]

theorem v6small_test_0058_step_0 : (40 : ℤ) = 2 * 15 + 10 := by
  norm_num

theorem v6small_test_0058_step_1 : (15 : ℤ) = 1 * 10 + 5 := by
  norm_num

theorem v6small_test_0058_step_2 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem v6small_test_0058_divides : (5 : ℤ) ∣ (-45 : ℤ) := by
  norm_num

theorem v6small_test_0058_conclusion : ∃ x y : ℤ, (-45 : ℤ) = (15 : ℤ) * x + (40 : ℤ) * y := by
  have hgcd : (Int.gcd (15 : ℤ) (40 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (15 : ℤ) (40 : ℤ) (-45 : ℤ)).2
  simpa [hgcd] using v6small_test_0058_divides

theorem v6small_test_0060_gcd : Nat.gcd 60 42 = 6 := by
  norm_num [Nat.gcd]

theorem v6small_test_0060_step_0 : (60 : ℤ) = 1 * 42 + 18 := by
  norm_num

theorem v6small_test_0060_step_1 : (42 : ℤ) = 2 * 18 + 6 := by
  norm_num

theorem v6small_test_0060_step_2 : (18 : ℤ) = 3 * 6 + 0 := by
  norm_num

theorem v6small_test_0060_divides : (6 : ℤ) ∣ (-24 : ℤ) := by
  norm_num

theorem v6small_test_0060_conclusion : ∃ x y : ℤ, (-24 : ℤ) = (60 : ℤ) * x + (42 : ℤ) * y := by
  have hgcd : (Int.gcd (60 : ℤ) (42 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (60 : ℤ) (42 : ℤ) (-24 : ℤ)).2
  simpa [hgcd] using v6small_test_0060_divides

theorem v6small_test_0062_gcd : Nat.gcd 135 72 = 9 := by
  norm_num [Nat.gcd]

theorem v6small_test_0062_step_0 : (135 : ℤ) = 1 * 72 + 63 := by
  norm_num

theorem v6small_test_0062_step_1 : (72 : ℤ) = 1 * 63 + 9 := by
  norm_num

theorem v6small_test_0062_step_2 : (63 : ℤ) = 7 * 9 + 0 := by
  norm_num

theorem v6small_test_0062_divides : (9 : ℤ) ∣ (-54 : ℤ) := by
  norm_num

theorem v6small_test_0062_conclusion : ∃ x y : ℤ, (-54 : ℤ) = (135 : ℤ) * x + (72 : ℤ) * y := by
  have hgcd : (Int.gcd (135 : ℤ) (72 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (135 : ℤ) (72 : ℤ) (-54 : ℤ)).2
  simpa [hgcd] using v6small_test_0062_divides

theorem v6small_test_0063_gcd : Nat.gcd 36 192 = 12 := by
  norm_num [Nat.gcd]

theorem v6small_test_0063_step_0 : (192 : ℤ) = 5 * 36 + 12 := by
  norm_num

theorem v6small_test_0063_step_1 : (36 : ℤ) = 3 * 12 + 0 := by
  norm_num

theorem v6small_test_0063_divides : ¬ (12 : ℤ) ∣ (163 : ℤ) := by
  norm_num

theorem v6small_test_0063_conclusion : ¬ (∃ x y : ℤ, (163 : ℤ) = (36 : ℤ) * x + (192 : ℤ) * y) := by
  have hgcd : (Int.gcd (36 : ℤ) (192 : ℤ) : ℤ) = 12 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (36 : ℤ) (192 : ℤ) (163 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0063_divides hd

theorem v6small_test_0064_gcd : Nat.gcd 88 96 = 8 := by
  norm_num [Nat.gcd]

theorem v6small_test_0064_step_0 : (96 : ℤ) = 1 * 88 + 8 := by
  norm_num

theorem v6small_test_0064_step_1 : (88 : ℤ) = 11 * 8 + 0 := by
  norm_num

theorem v6small_test_0064_divides : (8 : ℤ) ∣ (-32 : ℤ) := by
  norm_num

theorem v6small_test_0064_conclusion : ∃ x y : ℤ, (-32 : ℤ) = (88 : ℤ) * x + (96 : ℤ) * y := by
  have hgcd : (Int.gcd (88 : ℤ) (96 : ℤ) : ℤ) = 8 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (88 : ℤ) (96 : ℤ) (-32 : ℤ)).2
  simpa [hgcd] using v6small_test_0064_divides

theorem v6small_test_0067_gcd : Nat.gcd 132 60 = 12 := by
  norm_num [Nat.gcd]

theorem v6small_test_0067_step_0 : (132 : ℤ) = 2 * 60 + 12 := by
  norm_num

theorem v6small_test_0067_step_1 : (60 : ℤ) = 5 * 12 + 0 := by
  norm_num

theorem v6small_test_0067_divides : ¬ (12 : ℤ) ∣ (171 : ℤ) := by
  norm_num

theorem v6small_test_0067_conclusion : ¬ (∃ x y : ℤ, (171 : ℤ) = (132 : ℤ) * x + (60 : ℤ) * y) := by
  have hgcd : (Int.gcd (132 : ℤ) (60 : ℤ) : ℤ) = 12 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (132 : ℤ) (60 : ℤ) (171 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0067_divides hd

theorem v6small_test_0068_gcd : Nat.gcd 21 39 = 3 := by
  norm_num [Nat.gcd]

theorem v6small_test_0068_step_0 : (39 : ℤ) = 1 * 21 + 18 := by
  norm_num

theorem v6small_test_0068_step_1 : (21 : ℤ) = 1 * 18 + 3 := by
  norm_num

theorem v6small_test_0068_step_2 : (18 : ℤ) = 6 * 3 + 0 := by
  norm_num

theorem v6small_test_0068_divides : (3 : ℤ) ∣ (30 : ℤ) := by
  norm_num

theorem v6small_test_0068_conclusion : ∃ x y : ℤ, (30 : ℤ) = (21 : ℤ) * x + (39 : ℤ) * y := by
  have hgcd : (Int.gcd (21 : ℤ) (39 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (21 : ℤ) (39 : ℤ) (30 : ℤ)).2
  simpa [hgcd] using v6small_test_0068_divides

theorem v6small_test_0070_gcd : Nat.gcd 21 28 = 7 := by
  norm_num [Nat.gcd]

theorem v6small_test_0070_step_0 : (28 : ℤ) = 1 * 21 + 7 := by
  norm_num

theorem v6small_test_0070_step_1 : (21 : ℤ) = 3 * 7 + 0 := by
  norm_num

theorem v6small_test_0070_divides : (7 : ℤ) ∣ (-28 : ℤ) := by
  norm_num

theorem v6small_test_0070_conclusion : ∃ x y : ℤ, (-28 : ℤ) = (21 : ℤ) * x + (28 : ℤ) * y := by
  have hgcd : (Int.gcd (21 : ℤ) (28 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (21 : ℤ) (28 : ℤ) (-28 : ℤ)).2
  simpa [hgcd] using v6small_test_0070_divides

theorem v6small_test_0071_gcd : Nat.gcd 22 6 = 2 := by
  norm_num [Nat.gcd]

theorem v6small_test_0071_step_0 : (22 : ℤ) = 3 * 6 + 4 := by
  norm_num

theorem v6small_test_0071_step_1 : (6 : ℤ) = 1 * 4 + 2 := by
  norm_num

theorem v6small_test_0071_step_2 : (4 : ℤ) = 2 * 2 + 0 := by
  norm_num

theorem v6small_test_0071_divides : ¬ (2 : ℤ) ∣ (25 : ℤ) := by
  norm_num

theorem v6small_test_0071_conclusion : ¬ (∃ x y : ℤ, (25 : ℤ) = (22 : ℤ) * x + (6 : ℤ) * y) := by
  have hgcd : (Int.gcd (22 : ℤ) (6 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (22 : ℤ) (6 : ℤ) (25 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0071_divides hd

theorem v6small_test_0072_gcd : Nat.gcd 30 39 = 3 := by
  norm_num [Nat.gcd]

theorem v6small_test_0072_step_0 : (39 : ℤ) = 1 * 30 + 9 := by
  norm_num

theorem v6small_test_0072_step_1 : (30 : ℤ) = 3 * 9 + 3 := by
  norm_num

theorem v6small_test_0072_step_2 : (9 : ℤ) = 3 * 3 + 0 := by
  norm_num

theorem v6small_test_0072_divides : (3 : ℤ) ∣ (-21 : ℤ) := by
  norm_num

theorem v6small_test_0072_conclusion : ∃ x y : ℤ, (-21 : ℤ) = (30 : ℤ) * x + (39 : ℤ) * y := by
  have hgcd : (Int.gcd (30 : ℤ) (39 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (30 : ℤ) (39 : ℤ) (-21 : ℤ)).2
  simpa [hgcd] using v6small_test_0072_divides

theorem v6small_test_0073_gcd : Nat.gcd 40 25 = 5 := by
  norm_num [Nat.gcd]

theorem v6small_test_0073_step_0 : (40 : ℤ) = 1 * 25 + 15 := by
  norm_num

theorem v6small_test_0073_step_1 : (25 : ℤ) = 1 * 15 + 10 := by
  norm_num

theorem v6small_test_0073_step_2 : (15 : ℤ) = 1 * 10 + 5 := by
  norm_num

theorem v6small_test_0073_step_3 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem v6small_test_0073_divides : ¬ (5 : ℤ) ∣ (76 : ℤ) := by
  norm_num

theorem v6small_test_0073_conclusion : ¬ (∃ x y : ℤ, (76 : ℤ) = (40 : ℤ) * x + (25 : ℤ) * y) := by
  have hgcd : (Int.gcd (40 : ℤ) (25 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (40 : ℤ) (25 : ℤ) (76 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0073_divides hd

theorem v6small_test_0074_gcd : Nat.gcd 63 144 = 9 := by
  norm_num [Nat.gcd]

theorem v6small_test_0074_step_0 : (144 : ℤ) = 2 * 63 + 18 := by
  norm_num

theorem v6small_test_0074_step_1 : (63 : ℤ) = 3 * 18 + 9 := by
  norm_num

theorem v6small_test_0074_step_2 : (18 : ℤ) = 2 * 9 + 0 := by
  norm_num

theorem v6small_test_0074_divides : (9 : ℤ) ∣ (99 : ℤ) := by
  norm_num

theorem v6small_test_0074_conclusion : ∃ x y : ℤ, (99 : ℤ) = (63 : ℤ) * x + (144 : ℤ) * y := by
  have hgcd : (Int.gcd (63 : ℤ) (144 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (63 : ℤ) (144 : ℤ) (99 : ℤ)).2
  simpa [hgcd] using v6small_test_0074_divides

theorem v6small_test_0075_gcd : Nat.gcd 21 91 = 7 := by
  norm_num [Nat.gcd]

theorem v6small_test_0075_step_0 : (91 : ℤ) = 4 * 21 + 7 := by
  norm_num

theorem v6small_test_0075_step_1 : (21 : ℤ) = 3 * 7 + 0 := by
  norm_num

theorem v6small_test_0075_divides : ¬ (7 : ℤ) ∣ (-23 : ℤ) := by
  norm_num

theorem v6small_test_0075_conclusion : ¬ (∃ x y : ℤ, (-23 : ℤ) = (21 : ℤ) * x + (91 : ℤ) * y) := by
  have hgcd : (Int.gcd (21 : ℤ) (91 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (21 : ℤ) (91 : ℤ) (-23 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0075_divides hd

theorem v6small_test_0076_gcd : Nat.gcd 80 75 = 5 := by
  norm_num [Nat.gcd]

theorem v6small_test_0076_step_0 : (80 : ℤ) = 1 * 75 + 5 := by
  norm_num

theorem v6small_test_0076_step_1 : (75 : ℤ) = 15 * 5 + 0 := by
  norm_num

theorem v6small_test_0076_divides : (5 : ℤ) ∣ (-40 : ℤ) := by
  norm_num

theorem v6small_test_0076_conclusion : ∃ x y : ℤ, (-40 : ℤ) = (80 : ℤ) * x + (75 : ℤ) * y := by
  have hgcd : (Int.gcd (80 : ℤ) (75 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (80 : ℤ) (75 : ℤ) (-40 : ℤ)).2
  simpa [hgcd] using v6small_test_0076_divides

theorem v6small_test_0078_gcd : Nat.gcd 154 187 = 11 := by
  norm_num [Nat.gcd]

theorem v6small_test_0078_step_0 : (187 : ℤ) = 1 * 154 + 33 := by
  norm_num

theorem v6small_test_0078_step_1 : (154 : ℤ) = 4 * 33 + 22 := by
  norm_num

theorem v6small_test_0078_step_2 : (33 : ℤ) = 1 * 22 + 11 := by
  norm_num

theorem v6small_test_0078_step_3 : (22 : ℤ) = 2 * 11 + 0 := by
  norm_num

theorem v6small_test_0078_divides : (11 : ℤ) ∣ (11 : ℤ) := by
  norm_num

theorem v6small_test_0078_conclusion : ∃ x y : ℤ, (11 : ℤ) = (154 : ℤ) * x + (187 : ℤ) * y := by
  have hgcd : (Int.gcd (154 : ℤ) (187 : ℤ) : ℤ) = 11 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (154 : ℤ) (187 : ℤ) (11 : ℤ)).2
  simpa [hgcd] using v6small_test_0078_divides

theorem v6small_test_0079_gcd : Nat.gcd 6 15 = 3 := by
  norm_num [Nat.gcd]

theorem v6small_test_0079_step_0 : (15 : ℤ) = 2 * 6 + 3 := by
  norm_num

theorem v6small_test_0079_step_1 : (6 : ℤ) = 2 * 3 + 0 := by
  norm_num

theorem v6small_test_0079_divides : ¬ (3 : ℤ) ∣ (44 : ℤ) := by
  norm_num

theorem v6small_test_0079_conclusion : ¬ (∃ x y : ℤ, (44 : ℤ) = (6 : ℤ) * x + (15 : ℤ) * y) := by
  have hgcd : (Int.gcd (6 : ℤ) (15 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (6 : ℤ) (15 : ℤ) (44 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0079_divides hd

theorem v6small_test_0081_gcd : Nat.gcd 50 120 = 10 := by
  norm_num [Nat.gcd]

theorem v6small_test_0081_step_0 : (120 : ℤ) = 2 * 50 + 20 := by
  norm_num

theorem v6small_test_0081_step_1 : (50 : ℤ) = 2 * 20 + 10 := by
  norm_num

theorem v6small_test_0081_step_2 : (20 : ℤ) = 2 * 10 + 0 := by
  norm_num

theorem v6small_test_0081_divides : ¬ (10 : ℤ) ∣ (114 : ℤ) := by
  norm_num

theorem v6small_test_0081_conclusion : ¬ (∃ x y : ℤ, (114 : ℤ) = (50 : ℤ) * x + (120 : ℤ) * y) := by
  have hgcd : (Int.gcd (50 : ℤ) (120 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (50 : ℤ) (120 : ℤ) (114 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0081_divides hd

theorem v6small_test_0083_gcd : Nat.gcd 80 88 = 8 := by
  norm_num [Nat.gcd]

theorem v6small_test_0083_step_0 : (88 : ℤ) = 1 * 80 + 8 := by
  norm_num

theorem v6small_test_0083_step_1 : (80 : ℤ) = 10 * 8 + 0 := by
  norm_num

theorem v6small_test_0083_divides : ¬ (8 : ℤ) ∣ (-73 : ℤ) := by
  norm_num

theorem v6small_test_0083_conclusion : ¬ (∃ x y : ℤ, (-73 : ℤ) = (80 : ℤ) * x + (88 : ℤ) * y) := by
  have hgcd : (Int.gcd (80 : ℤ) (88 : ℤ) : ℤ) = 8 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (80 : ℤ) (88 : ℤ) (-73 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0083_divides hd

theorem v6small_test_0085_gcd : Nat.gcd 99 45 = 9 := by
  norm_num [Nat.gcd]

theorem v6small_test_0085_step_0 : (99 : ℤ) = 2 * 45 + 9 := by
  norm_num

theorem v6small_test_0085_step_1 : (45 : ℤ) = 5 * 9 + 0 := by
  norm_num

theorem v6small_test_0085_divides : ¬ (9 : ℤ) ∣ (-4 : ℤ) := by
  norm_num

theorem v6small_test_0085_conclusion : ¬ (∃ x y : ℤ, (-4 : ℤ) = (99 : ℤ) * x + (45 : ℤ) * y) := by
  have hgcd : (Int.gcd (99 : ℤ) (45 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (99 : ℤ) (45 : ℤ) (-4 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0085_divides hd

theorem v6small_test_0086_gcd : Nat.gcd 126 117 = 9 := by
  norm_num [Nat.gcd]

theorem v6small_test_0086_step_0 : (126 : ℤ) = 1 * 117 + 9 := by
  norm_num

theorem v6small_test_0086_step_1 : (117 : ℤ) = 13 * 9 + 0 := by
  norm_num

theorem v6small_test_0086_divides : (9 : ℤ) ∣ (45 : ℤ) := by
  norm_num

theorem v6small_test_0086_conclusion : ∃ x y : ℤ, (45 : ℤ) = (126 : ℤ) * x + (117 : ℤ) * y := by
  have hgcd : (Int.gcd (126 : ℤ) (117 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (126 : ℤ) (117 : ℤ) (45 : ℤ)).2
  simpa [hgcd] using v6small_test_0086_divides

theorem v6small_test_0087_gcd : Nat.gcd 117 135 = 9 := by
  norm_num [Nat.gcd]

theorem v6small_test_0087_step_0 : (135 : ℤ) = 1 * 117 + 18 := by
  norm_num

theorem v6small_test_0087_step_1 : (117 : ℤ) = 6 * 18 + 9 := by
  norm_num

theorem v6small_test_0087_step_2 : (18 : ℤ) = 2 * 9 + 0 := by
  norm_num

theorem v6small_test_0087_divides : ¬ (9 : ℤ) ∣ (26 : ℤ) := by
  norm_num

theorem v6small_test_0087_conclusion : ¬ (∃ x y : ℤ, (26 : ℤ) = (117 : ℤ) * x + (135 : ℤ) * y) := by
  have hgcd : (Int.gcd (117 : ℤ) (135 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (117 : ℤ) (135 : ℤ) (26 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0087_divides hd

theorem v6small_test_0088_gcd : Nat.gcd 40 16 = 8 := by
  norm_num [Nat.gcd]

theorem v6small_test_0088_step_0 : (40 : ℤ) = 2 * 16 + 8 := by
  norm_num

theorem v6small_test_0088_step_1 : (16 : ℤ) = 2 * 8 + 0 := by
  norm_num

theorem v6small_test_0088_divides : (8 : ℤ) ∣ (-112 : ℤ) := by
  norm_num

theorem v6small_test_0088_conclusion : ∃ x y : ℤ, (-112 : ℤ) = (40 : ℤ) * x + (16 : ℤ) * y := by
  have hgcd : (Int.gcd (40 : ℤ) (16 : ℤ) : ℤ) = 8 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (40 : ℤ) (16 : ℤ) (-112 : ℤ)).2
  simpa [hgcd] using v6small_test_0088_divides

theorem v6small_test_0089_gcd : Nat.gcd 24 9 = 3 := by
  norm_num [Nat.gcd]

theorem v6small_test_0089_step_0 : (24 : ℤ) = 2 * 9 + 6 := by
  norm_num

theorem v6small_test_0089_step_1 : (9 : ℤ) = 1 * 6 + 3 := by
  norm_num

theorem v6small_test_0089_step_2 : (6 : ℤ) = 2 * 3 + 0 := by
  norm_num

theorem v6small_test_0089_divides : ¬ (3 : ℤ) ∣ (19 : ℤ) := by
  norm_num

theorem v6small_test_0089_conclusion : ¬ (∃ x y : ℤ, (19 : ℤ) = (24 : ℤ) * x + (9 : ℤ) * y) := by
  have hgcd : (Int.gcd (24 : ℤ) (9 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (24 : ℤ) (9 : ℤ) (19 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0089_divides hd

theorem v6small_test_0090_gcd : Nat.gcd 6 14 = 2 := by
  norm_num [Nat.gcd]

theorem v6small_test_0090_step_0 : (14 : ℤ) = 2 * 6 + 2 := by
  norm_num

theorem v6small_test_0090_step_1 : (6 : ℤ) = 3 * 2 + 0 := by
  norm_num

theorem v6small_test_0090_divides : (2 : ℤ) ∣ (-26 : ℤ) := by
  norm_num

theorem v6small_test_0090_conclusion : ∃ x y : ℤ, (-26 : ℤ) = (6 : ℤ) * x + (14 : ℤ) * y := by
  have hgcd : (Int.gcd (6 : ℤ) (14 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (6 : ℤ) (14 : ℤ) (-26 : ℤ)).2
  simpa [hgcd] using v6small_test_0090_divides

theorem v6small_test_0092_gcd : Nat.gcd 77 63 = 7 := by
  norm_num [Nat.gcd]

theorem v6small_test_0092_step_0 : (77 : ℤ) = 1 * 63 + 14 := by
  norm_num

theorem v6small_test_0092_step_1 : (63 : ℤ) = 4 * 14 + 7 := by
  norm_num

theorem v6small_test_0092_step_2 : (14 : ℤ) = 2 * 7 + 0 := by
  norm_num

theorem v6small_test_0092_divides : (7 : ℤ) ∣ (70 : ℤ) := by
  norm_num

theorem v6small_test_0092_conclusion : ∃ x y : ℤ, (70 : ℤ) = (77 : ℤ) * x + (63 : ℤ) * y := by
  have hgcd : (Int.gcd (77 : ℤ) (63 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (77 : ℤ) (63 : ℤ) (70 : ℤ)).2
  simpa [hgcd] using v6small_test_0092_divides

theorem v6small_test_0093_gcd : Nat.gcd 36 26 = 2 := by
  norm_num [Nat.gcd]

theorem v6small_test_0093_step_0 : (36 : ℤ) = 1 * 26 + 10 := by
  norm_num

theorem v6small_test_0093_step_1 : (26 : ℤ) = 2 * 10 + 6 := by
  norm_num

theorem v6small_test_0093_step_2 : (10 : ℤ) = 1 * 6 + 4 := by
  norm_num

theorem v6small_test_0093_step_3 : (6 : ℤ) = 1 * 4 + 2 := by
  norm_num

theorem v6small_test_0093_step_4 : (4 : ℤ) = 2 * 2 + 0 := by
  norm_num

theorem v6small_test_0093_divides : ¬ (2 : ℤ) ∣ (21 : ℤ) := by
  norm_num

theorem v6small_test_0093_conclusion : ¬ (∃ x y : ℤ, (21 : ℤ) = (36 : ℤ) * x + (26 : ℤ) * y) := by
  have hgcd : (Int.gcd (36 : ℤ) (26 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (36 : ℤ) (26 : ℤ) (21 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0093_divides hd

theorem v6small_test_0094_gcd : Nat.gcd 75 35 = 5 := by
  norm_num [Nat.gcd]

theorem v6small_test_0094_step_0 : (75 : ℤ) = 2 * 35 + 5 := by
  norm_num

theorem v6small_test_0094_step_1 : (35 : ℤ) = 7 * 5 + 0 := by
  norm_num

theorem v6small_test_0094_divides : (5 : ℤ) ∣ (25 : ℤ) := by
  norm_num

theorem v6small_test_0094_conclusion : ∃ x y : ℤ, (25 : ℤ) = (75 : ℤ) * x + (35 : ℤ) * y := by
  have hgcd : (Int.gcd (75 : ℤ) (35 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (75 : ℤ) (35 : ℤ) (25 : ℤ)).2
  simpa [hgcd] using v6small_test_0094_divides

theorem v6small_test_0096_gcd : Nat.gcd 21 48 = 3 := by
  norm_num [Nat.gcd]

theorem v6small_test_0096_step_0 : (48 : ℤ) = 2 * 21 + 6 := by
  norm_num

theorem v6small_test_0096_step_1 : (21 : ℤ) = 3 * 6 + 3 := by
  norm_num

theorem v6small_test_0096_step_2 : (6 : ℤ) = 2 * 3 + 0 := by
  norm_num

theorem v6small_test_0096_divides : (3 : ℤ) ∣ (-15 : ℤ) := by
  norm_num

theorem v6small_test_0096_conclusion : ∃ x y : ℤ, (-15 : ℤ) = (21 : ℤ) * x + (48 : ℤ) * y := by
  have hgcd : (Int.gcd (21 : ℤ) (48 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (21 : ℤ) (48 : ℤ) (-15 : ℤ)).2
  simpa [hgcd] using v6small_test_0096_divides

theorem v6small_test_0097_gcd : Nat.gcd 90 99 = 9 := by
  norm_num [Nat.gcd]

theorem v6small_test_0097_step_0 : (99 : ℤ) = 1 * 90 + 9 := by
  norm_num

theorem v6small_test_0097_step_1 : (90 : ℤ) = 10 * 9 + 0 := by
  norm_num

theorem v6small_test_0097_divides : ¬ (9 : ℤ) ∣ (-31 : ℤ) := by
  norm_num

theorem v6small_test_0097_conclusion : ¬ (∃ x y : ℤ, (-31 : ℤ) = (90 : ℤ) * x + (99 : ℤ) * y) := by
  have hgcd : (Int.gcd (90 : ℤ) (99 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (90 : ℤ) (99 : ℤ) (-31 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0097_divides hd

theorem v6small_test_0098_gcd : Nat.gcd 156 180 = 12 := by
  norm_num [Nat.gcd]

theorem v6small_test_0098_step_0 : (180 : ℤ) = 1 * 156 + 24 := by
  norm_num

theorem v6small_test_0098_step_1 : (156 : ℤ) = 6 * 24 + 12 := by
  norm_num

theorem v6small_test_0098_step_2 : (24 : ℤ) = 2 * 12 + 0 := by
  norm_num

theorem v6small_test_0098_divides : (12 : ℤ) ∣ (60 : ℤ) := by
  norm_num

theorem v6small_test_0098_conclusion : ∃ x y : ℤ, (60 : ℤ) = (156 : ℤ) * x + (180 : ℤ) * y := by
  have hgcd : (Int.gcd (156 : ℤ) (180 : ℤ) : ℤ) = 12 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (156 : ℤ) (180 : ℤ) (60 : ℤ)).2
  simpa [hgcd] using v6small_test_0098_divides

theorem v6small_test_0099_gcd : Nat.gcd 60 36 = 12 := by
  norm_num [Nat.gcd]

theorem v6small_test_0099_step_0 : (60 : ℤ) = 1 * 36 + 24 := by
  norm_num

theorem v6small_test_0099_step_1 : (36 : ℤ) = 1 * 24 + 12 := by
  norm_num

theorem v6small_test_0099_step_2 : (24 : ℤ) = 2 * 12 + 0 := by
  norm_num

theorem v6small_test_0099_divides : ¬ (12 : ℤ) ∣ (16 : ℤ) := by
  norm_num

theorem v6small_test_0099_conclusion : ¬ (∃ x y : ℤ, (16 : ℤ) = (60 : ℤ) * x + (36 : ℤ) * y) := by
  have hgcd : (Int.gcd (60 : ℤ) (36 : ℤ) : ℤ) = 12 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (60 : ℤ) (36 : ℤ) (16 : ℤ)).1 h
  rw [hgcd] at hd
  exact v6small_test_0099_divides hd

end AtomicClaimCertificates
