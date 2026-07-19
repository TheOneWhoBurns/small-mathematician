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

theorem v7long_test_0003_gcd : Nat.gcd 38 68 = 2 := by
  norm_num [Nat.gcd]

theorem v7long_test_0003_step_0 : (68 : ℤ) = 1 * 38 + 30 := by
  norm_num

theorem v7long_test_0003_step_1 : (38 : ℤ) = 1 * 30 + 8 := by
  norm_num

theorem v7long_test_0003_step_2 : (30 : ℤ) = 3 * 8 + 6 := by
  norm_num

theorem v7long_test_0003_step_3 : (8 : ℤ) = 1 * 6 + 2 := by
  norm_num

theorem v7long_test_0003_step_4 : (6 : ℤ) = 3 * 2 + 0 := by
  norm_num

theorem v7long_test_0003_divides : ¬ (2 : ℤ) ∣ (-35 : ℤ) := by
  norm_num

theorem v7long_test_0003_conclusion : ¬ (∃ x y : ℤ, (-35 : ℤ) = (38 : ℤ) * x + (68 : ℤ) * y) := by
  have hgcd : (Int.gcd (38 : ℤ) (68 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (38 : ℤ) (68 : ℤ) (-35 : ℤ)).1 h
  rw [hgcd] at hd
  exact v7long_test_0003_divides hd

theorem v7long_test_0005_gcd : Nat.gcd 148 348 = 4 := by
  norm_num [Nat.gcd]

theorem v7long_test_0005_step_0 : (348 : ℤ) = 2 * 148 + 52 := by
  norm_num

theorem v7long_test_0005_step_1 : (148 : ℤ) = 2 * 52 + 44 := by
  norm_num

theorem v7long_test_0005_step_2 : (52 : ℤ) = 1 * 44 + 8 := by
  norm_num

theorem v7long_test_0005_step_3 : (44 : ℤ) = 5 * 8 + 4 := by
  norm_num

theorem v7long_test_0005_step_4 : (8 : ℤ) = 2 * 4 + 0 := by
  norm_num

theorem v7long_test_0005_divides : ¬ (4 : ℤ) ∣ (58 : ℤ) := by
  norm_num

theorem v7long_test_0005_conclusion : ¬ (∃ x y : ℤ, (58 : ℤ) = (148 : ℤ) * x + (348 : ℤ) * y) := by
  have hgcd : (Int.gcd (148 : ℤ) (348 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (148 : ℤ) (348 : ℤ) (58 : ℤ)).1 h
  rw [hgcd] at hd
  exact v7long_test_0005_divides hd

theorem v7long_test_0006_gcd : Nat.gcd 62 70 = 2 := by
  norm_num [Nat.gcd]

theorem v7long_test_0006_step_0 : (70 : ℤ) = 1 * 62 + 8 := by
  norm_num

theorem v7long_test_0006_step_1 : (62 : ℤ) = 7 * 8 + 6 := by
  norm_num

theorem v7long_test_0006_step_2 : (8 : ℤ) = 1 * 6 + 2 := by
  norm_num

theorem v7long_test_0006_step_3 : (6 : ℤ) = 3 * 2 + 0 := by
  norm_num

theorem v7long_test_0006_divides : (2 : ℤ) ∣ (32 : ℤ) := by
  norm_num

theorem v7long_test_0006_conclusion : ∃ x y : ℤ, (32 : ℤ) = (62 : ℤ) * x + (70 : ℤ) * y := by
  have hgcd : (Int.gcd (62 : ℤ) (70 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (62 : ℤ) (70 : ℤ) (32 : ℤ)).2
  simpa [hgcd] using v7long_test_0006_divides

theorem v7long_test_0008_gcd : Nat.gcd 204 94 = 2 := by
  norm_num [Nat.gcd]

theorem v7long_test_0008_step_0 : (204 : ℤ) = 2 * 94 + 16 := by
  norm_num

theorem v7long_test_0008_step_1 : (94 : ℤ) = 5 * 16 + 14 := by
  norm_num

theorem v7long_test_0008_step_2 : (16 : ℤ) = 1 * 14 + 2 := by
  norm_num

theorem v7long_test_0008_step_3 : (14 : ℤ) = 7 * 2 + 0 := by
  norm_num

theorem v7long_test_0008_divides : (2 : ℤ) ∣ (30 : ℤ) := by
  norm_num

theorem v7long_test_0008_conclusion : ∃ x y : ℤ, (30 : ℤ) = (204 : ℤ) * x + (94 : ℤ) * y := by
  have hgcd : (Int.gcd (204 : ℤ) (94 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (204 : ℤ) (94 : ℤ) (30 : ℤ)).2
  simpa [hgcd] using v7long_test_0008_divides

theorem v7long_test_0018_gcd : Nat.gcd 399 150 = 3 := by
  norm_num [Nat.gcd]

theorem v7long_test_0018_step_0 : (399 : ℤ) = 2 * 150 + 99 := by
  norm_num

theorem v7long_test_0018_step_1 : (150 : ℤ) = 1 * 99 + 51 := by
  norm_num

theorem v7long_test_0018_step_2 : (99 : ℤ) = 1 * 51 + 48 := by
  norm_num

theorem v7long_test_0018_step_3 : (51 : ℤ) = 1 * 48 + 3 := by
  norm_num

theorem v7long_test_0018_step_4 : (48 : ℤ) = 16 * 3 + 0 := by
  norm_num

theorem v7long_test_0018_divides : (3 : ℤ) ∣ (-6 : ℤ) := by
  norm_num

theorem v7long_test_0018_conclusion : ∃ x y : ℤ, (-6 : ℤ) = (399 : ℤ) * x + (150 : ℤ) * y := by
  have hgcd : (Int.gcd (399 : ℤ) (150 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (399 : ℤ) (150 : ℤ) (-6 : ℤ)).2
  simpa [hgcd] using v7long_test_0018_divides

theorem v7long_test_0019_gcd : Nat.gcd 102 159 = 3 := by
  norm_num [Nat.gcd]

theorem v7long_test_0019_step_0 : (159 : ℤ) = 1 * 102 + 57 := by
  norm_num

theorem v7long_test_0019_step_1 : (102 : ℤ) = 1 * 57 + 45 := by
  norm_num

theorem v7long_test_0019_step_2 : (57 : ℤ) = 1 * 45 + 12 := by
  norm_num

theorem v7long_test_0019_step_3 : (45 : ℤ) = 3 * 12 + 9 := by
  norm_num

theorem v7long_test_0019_step_4 : (12 : ℤ) = 1 * 9 + 3 := by
  norm_num

theorem v7long_test_0019_step_5 : (9 : ℤ) = 3 * 3 + 0 := by
  norm_num

theorem v7long_test_0019_divides : ¬ (3 : ℤ) ∣ (-20 : ℤ) := by
  norm_num

theorem v7long_test_0019_conclusion : ¬ (∃ x y : ℤ, (-20 : ℤ) = (102 : ℤ) * x + (159 : ℤ) * y) := by
  have hgcd : (Int.gcd (102 : ℤ) (159 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (102 : ℤ) (159 : ℤ) (-20 : ℤ)).1 h
  rw [hgcd] at hd
  exact v7long_test_0019_divides hd

theorem v7long_test_0022_gcd : Nat.gcd 154 210 = 14 := by
  norm_num [Nat.gcd]

theorem v7long_test_0022_step_0 : (210 : ℤ) = 1 * 154 + 56 := by
  norm_num

theorem v7long_test_0022_step_1 : (154 : ℤ) = 2 * 56 + 42 := by
  norm_num

theorem v7long_test_0022_step_2 : (56 : ℤ) = 1 * 42 + 14 := by
  norm_num

theorem v7long_test_0022_step_3 : (42 : ℤ) = 3 * 14 + 0 := by
  norm_num

theorem v7long_test_0022_divides : (14 : ℤ) ∣ (-70 : ℤ) := by
  norm_num

theorem v7long_test_0022_conclusion : ∃ x y : ℤ, (-70 : ℤ) = (154 : ℤ) * x + (210 : ℤ) * y := by
  have hgcd : (Int.gcd (154 : ℤ) (210 : ℤ) : ℤ) = 14 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (154 : ℤ) (210 : ℤ) (-70 : ℤ)).2
  simpa [hgcd] using v7long_test_0022_divides

theorem v7long_test_0024_gcd : Nat.gcd 762 432 = 6 := by
  norm_num [Nat.gcd]

theorem v7long_test_0024_step_0 : (762 : ℤ) = 1 * 432 + 330 := by
  norm_num

theorem v7long_test_0024_step_1 : (432 : ℤ) = 1 * 330 + 102 := by
  norm_num

theorem v7long_test_0024_step_2 : (330 : ℤ) = 3 * 102 + 24 := by
  norm_num

theorem v7long_test_0024_step_3 : (102 : ℤ) = 4 * 24 + 6 := by
  norm_num

theorem v7long_test_0024_step_4 : (24 : ℤ) = 4 * 6 + 0 := by
  norm_num

theorem v7long_test_0024_divides : (6 : ℤ) ∣ (-48 : ℤ) := by
  norm_num

theorem v7long_test_0024_conclusion : ∃ x y : ℤ, (-48 : ℤ) = (762 : ℤ) * x + (432 : ℤ) * y := by
  have hgcd : (Int.gcd (762 : ℤ) (432 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (762 : ℤ) (432 : ℤ) (-48 : ℤ)).2
  simpa [hgcd] using v7long_test_0024_divides

theorem v7long_test_0025_gcd : Nat.gcd 399 216 = 3 := by
  norm_num [Nat.gcd]

theorem v7long_test_0025_step_0 : (399 : ℤ) = 1 * 216 + 183 := by
  norm_num

theorem v7long_test_0025_step_1 : (216 : ℤ) = 1 * 183 + 33 := by
  norm_num

theorem v7long_test_0025_step_2 : (183 : ℤ) = 5 * 33 + 18 := by
  norm_num

theorem v7long_test_0025_step_3 : (33 : ℤ) = 1 * 18 + 15 := by
  norm_num

theorem v7long_test_0025_step_4 : (18 : ℤ) = 1 * 15 + 3 := by
  norm_num

theorem v7long_test_0025_step_5 : (15 : ℤ) = 5 * 3 + 0 := by
  norm_num

theorem v7long_test_0025_divides : ¬ (3 : ℤ) ∣ (26 : ℤ) := by
  norm_num

theorem v7long_test_0025_conclusion : ¬ (∃ x y : ℤ, (26 : ℤ) = (399 : ℤ) * x + (216 : ℤ) * y) := by
  have hgcd : (Int.gcd (399 : ℤ) (216 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (399 : ℤ) (216 : ℤ) (26 : ℤ)).1 h
  rw [hgcd] at hd
  exact v7long_test_0025_divides hd

theorem v7long_test_0028_gcd : Nat.gcd 75 138 = 3 := by
  norm_num [Nat.gcd]

theorem v7long_test_0028_step_0 : (138 : ℤ) = 1 * 75 + 63 := by
  norm_num

theorem v7long_test_0028_step_1 : (75 : ℤ) = 1 * 63 + 12 := by
  norm_num

theorem v7long_test_0028_step_2 : (63 : ℤ) = 5 * 12 + 3 := by
  norm_num

theorem v7long_test_0028_step_3 : (12 : ℤ) = 4 * 3 + 0 := by
  norm_num

theorem v7long_test_0028_divides : (3 : ℤ) ∣ (63 : ℤ) := by
  norm_num

theorem v7long_test_0028_conclusion : ∃ x y : ℤ, (63 : ℤ) = (75 : ℤ) * x + (138 : ℤ) * y := by
  have hgcd : (Int.gcd (75 : ℤ) (138 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (75 : ℤ) (138 : ℤ) (63 : ℤ)).2
  simpa [hgcd] using v7long_test_0028_divides

theorem v7long_test_0033_gcd : Nat.gcd 226 140 = 2 := by
  norm_num [Nat.gcd]

theorem v7long_test_0033_step_0 : (226 : ℤ) = 1 * 140 + 86 := by
  norm_num

theorem v7long_test_0033_step_1 : (140 : ℤ) = 1 * 86 + 54 := by
  norm_num

theorem v7long_test_0033_step_2 : (86 : ℤ) = 1 * 54 + 32 := by
  norm_num

theorem v7long_test_0033_step_3 : (54 : ℤ) = 1 * 32 + 22 := by
  norm_num

theorem v7long_test_0033_step_4 : (32 : ℤ) = 1 * 22 + 10 := by
  norm_num

theorem v7long_test_0033_step_5 : (22 : ℤ) = 2 * 10 + 2 := by
  norm_num

theorem v7long_test_0033_step_6 : (10 : ℤ) = 5 * 2 + 0 := by
  norm_num

theorem v7long_test_0033_divides : ¬ (2 : ℤ) ∣ (-19 : ℤ) := by
  norm_num

theorem v7long_test_0033_conclusion : ¬ (∃ x y : ℤ, (-19 : ℤ) = (226 : ℤ) * x + (140 : ℤ) * y) := by
  have hgcd : (Int.gcd (226 : ℤ) (140 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (226 : ℤ) (140 : ℤ) (-19 : ℤ)).1 h
  rw [hgcd] at hd
  exact v7long_test_0033_divides hd

theorem v7long_test_0041_gcd : Nat.gcd 24 130 = 2 := by
  norm_num [Nat.gcd]

theorem v7long_test_0041_step_0 : (130 : ℤ) = 5 * 24 + 10 := by
  norm_num

theorem v7long_test_0041_step_1 : (24 : ℤ) = 2 * 10 + 4 := by
  norm_num

theorem v7long_test_0041_step_2 : (10 : ℤ) = 2 * 4 + 2 := by
  norm_num

theorem v7long_test_0041_step_3 : (4 : ℤ) = 2 * 2 + 0 := by
  norm_num

theorem v7long_test_0041_divides : ¬ (2 : ℤ) ∣ (45 : ℤ) := by
  norm_num

theorem v7long_test_0041_conclusion : ¬ (∃ x y : ℤ, (45 : ℤ) = (24 : ℤ) * x + (130 : ℤ) * y) := by
  have hgcd : (Int.gcd (24 : ℤ) (130 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (24 : ℤ) (130 : ℤ) (45 : ℤ)).1 h
  rw [hgcd] at hd
  exact v7long_test_0041_divides hd

theorem v7long_test_0054_gcd : Nat.gcd 840 435 = 15 := by
  norm_num [Nat.gcd]

theorem v7long_test_0054_step_0 : (840 : ℤ) = 1 * 435 + 405 := by
  norm_num

theorem v7long_test_0054_step_1 : (435 : ℤ) = 1 * 405 + 30 := by
  norm_num

theorem v7long_test_0054_step_2 : (405 : ℤ) = 13 * 30 + 15 := by
  norm_num

theorem v7long_test_0054_step_3 : (30 : ℤ) = 2 * 15 + 0 := by
  norm_num

theorem v7long_test_0054_divides : (15 : ℤ) ∣ (-210 : ℤ) := by
  norm_num

theorem v7long_test_0054_conclusion : ∃ x y : ℤ, (-210 : ℤ) = (840 : ℤ) * x + (435 : ℤ) * y := by
  have hgcd : (Int.gcd (840 : ℤ) (435 : ℤ) : ℤ) = 15 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (840 : ℤ) (435 : ℤ) (-210 : ℤ)).2
  simpa [hgcd] using v7long_test_0054_divides

theorem v7long_test_0055_gcd : Nat.gcd 483 350 = 7 := by
  norm_num [Nat.gcd]

theorem v7long_test_0055_step_0 : (483 : ℤ) = 1 * 350 + 133 := by
  norm_num

theorem v7long_test_0055_step_1 : (350 : ℤ) = 2 * 133 + 84 := by
  norm_num

theorem v7long_test_0055_step_2 : (133 : ℤ) = 1 * 84 + 49 := by
  norm_num

theorem v7long_test_0055_step_3 : (84 : ℤ) = 1 * 49 + 35 := by
  norm_num

theorem v7long_test_0055_step_4 : (49 : ℤ) = 1 * 35 + 14 := by
  norm_num

theorem v7long_test_0055_step_5 : (35 : ℤ) = 2 * 14 + 7 := by
  norm_num

theorem v7long_test_0055_step_6 : (14 : ℤ) = 2 * 7 + 0 := by
  norm_num

theorem v7long_test_0055_divides : ¬ (7 : ℤ) ∣ (-89 : ℤ) := by
  norm_num

theorem v7long_test_0055_conclusion : ¬ (∃ x y : ℤ, (-89 : ℤ) = (483 : ℤ) * x + (350 : ℤ) * y) := by
  have hgcd : (Int.gcd (483 : ℤ) (350 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (483 : ℤ) (350 : ℤ) (-89 : ℤ)).1 h
  rw [hgcd] at hd
  exact v7long_test_0055_divides hd

theorem v7long_test_0057_gcd : Nat.gcd 366 346 = 2 := by
  norm_num [Nat.gcd]

theorem v7long_test_0057_step_0 : (366 : ℤ) = 1 * 346 + 20 := by
  norm_num

theorem v7long_test_0057_step_1 : (346 : ℤ) = 17 * 20 + 6 := by
  norm_num

theorem v7long_test_0057_step_2 : (20 : ℤ) = 3 * 6 + 2 := by
  norm_num

theorem v7long_test_0057_step_3 : (6 : ℤ) = 3 * 2 + 0 := by
  norm_num

theorem v7long_test_0057_divides : ¬ (2 : ℤ) ∣ (21 : ℤ) := by
  norm_num

theorem v7long_test_0057_conclusion : ¬ (∃ x y : ℤ, (21 : ℤ) = (366 : ℤ) * x + (346 : ℤ) * y) := by
  have hgcd : (Int.gcd (366 : ℤ) (346 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (366 : ℤ) (346 : ℤ) (21 : ℤ)).1 h
  rw [hgcd] at hd
  exact v7long_test_0057_divides hd

theorem v7long_test_0058_gcd : Nat.gcd 840 688 = 8 := by
  norm_num [Nat.gcd]

theorem v7long_test_0058_step_0 : (840 : ℤ) = 1 * 688 + 152 := by
  norm_num

theorem v7long_test_0058_step_1 : (688 : ℤ) = 4 * 152 + 80 := by
  norm_num

theorem v7long_test_0058_step_2 : (152 : ℤ) = 1 * 80 + 72 := by
  norm_num

theorem v7long_test_0058_step_3 : (80 : ℤ) = 1 * 72 + 8 := by
  norm_num

theorem v7long_test_0058_step_4 : (72 : ℤ) = 9 * 8 + 0 := by
  norm_num

theorem v7long_test_0058_divides : (8 : ℤ) ∣ (152 : ℤ) := by
  norm_num

theorem v7long_test_0058_conclusion : ∃ x y : ℤ, (152 : ℤ) = (840 : ℤ) * x + (688 : ℤ) * y := by
  have hgcd : (Int.gcd (840 : ℤ) (688 : ℤ) : ℤ) = 8 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (840 : ℤ) (688 : ℤ) (152 : ℤ)).2
  simpa [hgcd] using v7long_test_0058_divides

theorem v7long_test_0063_gcd : Nat.gcd 624 171 = 3 := by
  norm_num [Nat.gcd]

theorem v7long_test_0063_step_0 : (624 : ℤ) = 3 * 171 + 111 := by
  norm_num

theorem v7long_test_0063_step_1 : (171 : ℤ) = 1 * 111 + 60 := by
  norm_num

theorem v7long_test_0063_step_2 : (111 : ℤ) = 1 * 60 + 51 := by
  norm_num

theorem v7long_test_0063_step_3 : (60 : ℤ) = 1 * 51 + 9 := by
  norm_num

theorem v7long_test_0063_step_4 : (51 : ℤ) = 5 * 9 + 6 := by
  norm_num

theorem v7long_test_0063_step_5 : (9 : ℤ) = 1 * 6 + 3 := by
  norm_num

theorem v7long_test_0063_step_6 : (6 : ℤ) = 2 * 3 + 0 := by
  norm_num

theorem v7long_test_0063_divides : ¬ (3 : ℤ) ∣ (4 : ℤ) := by
  norm_num

theorem v7long_test_0063_conclusion : ¬ (∃ x y : ℤ, (4 : ℤ) = (624 : ℤ) * x + (171 : ℤ) * y) := by
  have hgcd : (Int.gcd (624 : ℤ) (171 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (624 : ℤ) (171 : ℤ) (4 : ℤ)).1 h
  rw [hgcd] at hd
  exact v7long_test_0063_divides hd

theorem v7long_test_0077_gcd : Nat.gcd 963 918 = 9 := by
  norm_num [Nat.gcd]

theorem v7long_test_0077_step_0 : (963 : ℤ) = 1 * 918 + 45 := by
  norm_num

theorem v7long_test_0077_step_1 : (918 : ℤ) = 20 * 45 + 18 := by
  norm_num

theorem v7long_test_0077_step_2 : (45 : ℤ) = 2 * 18 + 9 := by
  norm_num

theorem v7long_test_0077_step_3 : (18 : ℤ) = 2 * 9 + 0 := by
  norm_num

theorem v7long_test_0077_divides : ¬ (9 : ℤ) ∣ (-202 : ℤ) := by
  norm_num

theorem v7long_test_0077_conclusion : ¬ (∃ x y : ℤ, (-202 : ℤ) = (963 : ℤ) * x + (918 : ℤ) * y) := by
  have hgcd : (Int.gcd (963 : ℤ) (918 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (963 : ℤ) (918 : ℤ) (-202 : ℤ)).1 h
  rw [hgcd] at hd
  exact v7long_test_0077_divides hd

theorem v7long_test_0078_gcd : Nat.gcd 832 308 = 4 := by
  norm_num [Nat.gcd]

theorem v7long_test_0078_step_0 : (832 : ℤ) = 2 * 308 + 216 := by
  norm_num

theorem v7long_test_0078_step_1 : (308 : ℤ) = 1 * 216 + 92 := by
  norm_num

theorem v7long_test_0078_step_2 : (216 : ℤ) = 2 * 92 + 32 := by
  norm_num

theorem v7long_test_0078_step_3 : (92 : ℤ) = 2 * 32 + 28 := by
  norm_num

theorem v7long_test_0078_step_4 : (32 : ℤ) = 1 * 28 + 4 := by
  norm_num

theorem v7long_test_0078_step_5 : (28 : ℤ) = 7 * 4 + 0 := by
  norm_num

theorem v7long_test_0078_divides : (4 : ℤ) ∣ (-8 : ℤ) := by
  norm_num

theorem v7long_test_0078_conclusion : ∃ x y : ℤ, (-8 : ℤ) = (832 : ℤ) * x + (308 : ℤ) * y := by
  have hgcd : (Int.gcd (832 : ℤ) (308 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (832 : ℤ) (308 : ℤ) (-8 : ℤ)).2
  simpa [hgcd] using v7long_test_0078_divides

theorem v7long_test_0080_gcd : Nat.gcd 621 874 = 23 := by
  norm_num [Nat.gcd]

theorem v7long_test_0080_step_0 : (874 : ℤ) = 1 * 621 + 253 := by
  norm_num

theorem v7long_test_0080_step_1 : (621 : ℤ) = 2 * 253 + 115 := by
  norm_num

theorem v7long_test_0080_step_2 : (253 : ℤ) = 2 * 115 + 23 := by
  norm_num

theorem v7long_test_0080_step_3 : (115 : ℤ) = 5 * 23 + 0 := by
  norm_num

theorem v7long_test_0080_divides : (23 : ℤ) ∣ (-207 : ℤ) := by
  norm_num

theorem v7long_test_0080_conclusion : ∃ x y : ℤ, (-207 : ℤ) = (621 : ℤ) * x + (874 : ℤ) * y := by
  have hgcd : (Int.gcd (621 : ℤ) (874 : ℤ) : ℤ) = 23 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (621 : ℤ) (874 : ℤ) (-207 : ℤ)).2
  simpa [hgcd] using v7long_test_0080_divides

theorem v7long_test_0088_gcd : Nat.gcd 644 432 = 4 := by
  norm_num [Nat.gcd]

theorem v7long_test_0088_step_0 : (644 : ℤ) = 1 * 432 + 212 := by
  norm_num

theorem v7long_test_0088_step_1 : (432 : ℤ) = 2 * 212 + 8 := by
  norm_num

theorem v7long_test_0088_step_2 : (212 : ℤ) = 26 * 8 + 4 := by
  norm_num

theorem v7long_test_0088_step_3 : (8 : ℤ) = 2 * 4 + 0 := by
  norm_num

theorem v7long_test_0088_divides : (4 : ℤ) ∣ (-96 : ℤ) := by
  norm_num

theorem v7long_test_0088_conclusion : ∃ x y : ℤ, (-96 : ℤ) = (644 : ℤ) * x + (432 : ℤ) * y := by
  have hgcd : (Int.gcd (644 : ℤ) (432 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (644 : ℤ) (432 : ℤ) (-96 : ℤ)).2
  simpa [hgcd] using v7long_test_0088_divides

theorem v7long_test_0090_gcd : Nat.gcd 166 22 = 2 := by
  norm_num [Nat.gcd]

theorem v7long_test_0090_step_0 : (166 : ℤ) = 7 * 22 + 12 := by
  norm_num

theorem v7long_test_0090_step_1 : (22 : ℤ) = 1 * 12 + 10 := by
  norm_num

theorem v7long_test_0090_step_2 : (12 : ℤ) = 1 * 10 + 2 := by
  norm_num

theorem v7long_test_0090_step_3 : (10 : ℤ) = 5 * 2 + 0 := by
  norm_num

theorem v7long_test_0090_divides : (2 : ℤ) ∣ (28 : ℤ) := by
  norm_num

theorem v7long_test_0090_conclusion : ∃ x y : ℤ, (28 : ℤ) = (166 : ℤ) * x + (22 : ℤ) * y := by
  have hgcd : (Int.gcd (166 : ℤ) (22 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (166 : ℤ) (22 : ℤ) (28 : ℤ)).2
  simpa [hgcd] using v7long_test_0090_divides

theorem v7long_test_0091_gcd : Nat.gcd 891 630 = 9 := by
  norm_num [Nat.gcd]

theorem v7long_test_0091_step_0 : (891 : ℤ) = 1 * 630 + 261 := by
  norm_num

theorem v7long_test_0091_step_1 : (630 : ℤ) = 2 * 261 + 108 := by
  norm_num

theorem v7long_test_0091_step_2 : (261 : ℤ) = 2 * 108 + 45 := by
  norm_num

theorem v7long_test_0091_step_3 : (108 : ℤ) = 2 * 45 + 18 := by
  norm_num

theorem v7long_test_0091_step_4 : (45 : ℤ) = 2 * 18 + 9 := by
  norm_num

theorem v7long_test_0091_step_5 : (18 : ℤ) = 2 * 9 + 0 := by
  norm_num

theorem v7long_test_0091_divides : ¬ (9 : ℤ) ∣ (41 : ℤ) := by
  norm_num

theorem v7long_test_0091_conclusion : ¬ (∃ x y : ℤ, (41 : ℤ) = (891 : ℤ) * x + (630 : ℤ) * y) := by
  have hgcd : (Int.gcd (891 : ℤ) (630 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (891 : ℤ) (630 : ℤ) (41 : ℤ)).1 h
  rw [hgcd] at hd
  exact v7long_test_0091_divides hd

theorem v7long_test_0094_gcd : Nat.gcd 120 208 = 8 := by
  norm_num [Nat.gcd]

theorem v7long_test_0094_step_0 : (208 : ℤ) = 1 * 120 + 88 := by
  norm_num

theorem v7long_test_0094_step_1 : (120 : ℤ) = 1 * 88 + 32 := by
  norm_num

theorem v7long_test_0094_step_2 : (88 : ℤ) = 2 * 32 + 24 := by
  norm_num

theorem v7long_test_0094_step_3 : (32 : ℤ) = 1 * 24 + 8 := by
  norm_num

theorem v7long_test_0094_step_4 : (24 : ℤ) = 3 * 8 + 0 := by
  norm_num

theorem v7long_test_0094_divides : (8 : ℤ) ∣ (-16 : ℤ) := by
  norm_num

theorem v7long_test_0094_conclusion : ∃ x y : ℤ, (-16 : ℤ) = (120 : ℤ) * x + (208 : ℤ) * y := by
  have hgcd : (Int.gcd (120 : ℤ) (208 : ℤ) : ℤ) = 8 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (120 : ℤ) (208 : ℤ) (-16 : ℤ)).2
  simpa [hgcd] using v7long_test_0094_divides

theorem v7long_test_0097_gcd : Nat.gcd 984 408 = 24 := by
  norm_num [Nat.gcd]

theorem v7long_test_0097_step_0 : (984 : ℤ) = 2 * 408 + 168 := by
  norm_num

theorem v7long_test_0097_step_1 : (408 : ℤ) = 2 * 168 + 72 := by
  norm_num

theorem v7long_test_0097_step_2 : (168 : ℤ) = 2 * 72 + 24 := by
  norm_num

theorem v7long_test_0097_step_3 : (72 : ℤ) = 3 * 24 + 0 := by
  norm_num

theorem v7long_test_0097_divides : ¬ (24 : ℤ) ∣ (-26 : ℤ) := by
  norm_num

theorem v7long_test_0097_conclusion : ¬ (∃ x y : ℤ, (-26 : ℤ) = (984 : ℤ) * x + (408 : ℤ) * y) := by
  have hgcd : (Int.gcd (984 : ℤ) (408 : ℤ) : ℤ) = 24 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (984 : ℤ) (408 : ℤ) (-26 : ℤ)).1 h
  rw [hgcd] at hd
  exact v7long_test_0097_divides hd

theorem v7long_test_0098_gcd : Nat.gcd 465 250 = 5 := by
  norm_num [Nat.gcd]

theorem v7long_test_0098_step_0 : (465 : ℤ) = 1 * 250 + 215 := by
  norm_num

theorem v7long_test_0098_step_1 : (250 : ℤ) = 1 * 215 + 35 := by
  norm_num

theorem v7long_test_0098_step_2 : (215 : ℤ) = 6 * 35 + 5 := by
  norm_num

theorem v7long_test_0098_step_3 : (35 : ℤ) = 7 * 5 + 0 := by
  norm_num

theorem v7long_test_0098_divides : (5 : ℤ) ∣ (-65 : ℤ) := by
  norm_num

theorem v7long_test_0098_conclusion : ∃ x y : ℤ, (-65 : ℤ) = (465 : ℤ) * x + (250 : ℤ) * y := by
  have hgcd : (Int.gcd (465 : ℤ) (250 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (465 : ℤ) (250 : ℤ) (-65 : ℤ)).2
  simpa [hgcd] using v7long_test_0098_divides

theorem v7short_test_0016_gcd : Nat.gcd 630 606 = 6 := by
  norm_num [Nat.gcd]

theorem v7short_test_0016_step_0 : (630 : ℤ) = 1 * 606 + 24 := by
  norm_num

theorem v7short_test_0016_step_1 : (606 : ℤ) = 25 * 24 + 6 := by
  norm_num

theorem v7short_test_0016_step_2 : (24 : ℤ) = 4 * 6 + 0 := by
  norm_num

theorem v7short_test_0016_divides : (6 : ℤ) ∣ (126 : ℤ) := by
  norm_num

theorem v7short_test_0016_conclusion : ∃ x y : ℤ, (126 : ℤ) = (630 : ℤ) * x + (606 : ℤ) * y := by
  have hgcd : (Int.gcd (630 : ℤ) (606 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (630 : ℤ) (606 : ℤ) (126 : ℤ)).2
  simpa [hgcd] using v7short_test_0016_divides

theorem v7short_test_0019_gcd : Nat.gcd 62 74 = 2 := by
  norm_num [Nat.gcd]

theorem v7short_test_0019_step_0 : (74 : ℤ) = 1 * 62 + 12 := by
  norm_num

theorem v7short_test_0019_step_1 : (62 : ℤ) = 5 * 12 + 2 := by
  norm_num

theorem v7short_test_0019_step_2 : (12 : ℤ) = 6 * 2 + 0 := by
  norm_num

theorem v7short_test_0019_divides : ¬ (2 : ℤ) ∣ (49 : ℤ) := by
  norm_num

theorem v7short_test_0019_conclusion : ¬ (∃ x y : ℤ, (49 : ℤ) = (62 : ℤ) * x + (74 : ℤ) * y) := by
  have hgcd : (Int.gcd (62 : ℤ) (74 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (62 : ℤ) (74 : ℤ) (49 : ℤ)).1 h
  rw [hgcd] at hd
  exact v7short_test_0019_divides hd

theorem v7short_test_0031_gcd : Nat.gcd 20 245 = 5 := by
  norm_num [Nat.gcd]

theorem v7short_test_0031_step_0 : (245 : ℤ) = 12 * 20 + 5 := by
  norm_num

theorem v7short_test_0031_step_1 : (20 : ℤ) = 4 * 5 + 0 := by
  norm_num

theorem v7short_test_0031_divides : ¬ (5 : ℤ) ∣ (11 : ℤ) := by
  norm_num

theorem v7short_test_0031_conclusion : ¬ (∃ x y : ℤ, (11 : ℤ) = (20 : ℤ) * x + (245 : ℤ) * y) := by
  have hgcd : (Int.gcd (20 : ℤ) (245 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (20 : ℤ) (245 : ℤ) (11 : ℤ)).1 h
  rw [hgcd] at hd
  exact v7short_test_0031_divides hd

theorem v7short_test_0032_gcd : Nat.gcd 16 712 = 8 := by
  norm_num [Nat.gcd]

theorem v7short_test_0032_step_0 : (712 : ℤ) = 44 * 16 + 8 := by
  norm_num

theorem v7short_test_0032_step_1 : (16 : ℤ) = 2 * 8 + 0 := by
  norm_num

theorem v7short_test_0032_divides : (8 : ℤ) ∣ (32 : ℤ) := by
  norm_num

theorem v7short_test_0032_conclusion : ∃ x y : ℤ, (32 : ℤ) = (16 : ℤ) * x + (712 : ℤ) * y := by
  have hgcd : (Int.gcd (16 : ℤ) (712 : ℤ) : ℤ) = 8 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (16 : ℤ) (712 : ℤ) (32 : ℤ)).2
  simpa [hgcd] using v7short_test_0032_divides

theorem v7short_test_0033_gcd : Nat.gcd 968 480 = 8 := by
  norm_num [Nat.gcd]

theorem v7short_test_0033_step_0 : (968 : ℤ) = 2 * 480 + 8 := by
  norm_num

theorem v7short_test_0033_step_1 : (480 : ℤ) = 60 * 8 + 0 := by
  norm_num

theorem v7short_test_0033_divides : ¬ (8 : ℤ) ∣ (171 : ℤ) := by
  norm_num

theorem v7short_test_0033_conclusion : ¬ (∃ x y : ℤ, (171 : ℤ) = (968 : ℤ) * x + (480 : ℤ) * y) := by
  have hgcd : (Int.gcd (968 : ℤ) (480 : ℤ) : ℤ) = 8 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (968 : ℤ) (480 : ℤ) (171 : ℤ)).1 h
  rw [hgcd] at hd
  exact v7short_test_0033_divides hd

theorem v7short_test_0034_gcd : Nat.gcd 420 224 = 28 := by
  norm_num [Nat.gcd]

theorem v7short_test_0034_step_0 : (420 : ℤ) = 1 * 224 + 196 := by
  norm_num

theorem v7short_test_0034_step_1 : (224 : ℤ) = 1 * 196 + 28 := by
  norm_num

theorem v7short_test_0034_step_2 : (196 : ℤ) = 7 * 28 + 0 := by
  norm_num

theorem v7short_test_0034_divides : (28 : ℤ) ∣ (448 : ℤ) := by
  norm_num

theorem v7short_test_0034_conclusion : ∃ x y : ℤ, (448 : ℤ) = (420 : ℤ) * x + (224 : ℤ) * y := by
  have hgcd : (Int.gcd (420 : ℤ) (224 : ℤ) : ℤ) = 28 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (420 : ℤ) (224 : ℤ) (448 : ℤ)).2
  simpa [hgcd] using v7short_test_0034_divides

theorem v7short_test_0038_gcd : Nat.gcd 90 330 = 30 := by
  norm_num [Nat.gcd]

theorem v7short_test_0038_step_0 : (330 : ℤ) = 3 * 90 + 60 := by
  norm_num

theorem v7short_test_0038_step_1 : (90 : ℤ) = 1 * 60 + 30 := by
  norm_num

theorem v7short_test_0038_step_2 : (60 : ℤ) = 2 * 30 + 0 := by
  norm_num

theorem v7short_test_0038_divides : (30 : ℤ) ∣ (-570 : ℤ) := by
  norm_num

theorem v7short_test_0038_conclusion : ∃ x y : ℤ, (-570 : ℤ) = (90 : ℤ) * x + (330 : ℤ) * y := by
  have hgcd : (Int.gcd (90 : ℤ) (330 : ℤ) : ℤ) = 30 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (90 : ℤ) (330 : ℤ) (-570 : ℤ)).2
  simpa [hgcd] using v7short_test_0038_divides

theorem v7short_test_0042_gcd : Nat.gcd 60 200 = 20 := by
  norm_num [Nat.gcd]

theorem v7short_test_0042_step_0 : (200 : ℤ) = 3 * 60 + 20 := by
  norm_num

theorem v7short_test_0042_step_1 : (60 : ℤ) = 3 * 20 + 0 := by
  norm_num

theorem v7short_test_0042_divides : (20 : ℤ) ∣ (-60 : ℤ) := by
  norm_num

theorem v7short_test_0042_conclusion : ∃ x y : ℤ, (-60 : ℤ) = (60 : ℤ) * x + (200 : ℤ) * y := by
  have hgcd : (Int.gcd (60 : ℤ) (200 : ℤ) : ℤ) = 20 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (60 : ℤ) (200 : ℤ) (-60 : ℤ)).2
  simpa [hgcd] using v7short_test_0042_divides

theorem v7short_test_0048_gcd : Nat.gcd 770 392 = 14 := by
  norm_num [Nat.gcd]

theorem v7short_test_0048_step_0 : (770 : ℤ) = 1 * 392 + 378 := by
  norm_num

theorem v7short_test_0048_step_1 : (392 : ℤ) = 1 * 378 + 14 := by
  norm_num

theorem v7short_test_0048_step_2 : (378 : ℤ) = 27 * 14 + 0 := by
  norm_num

theorem v7short_test_0048_divides : (14 : ℤ) ∣ (-294 : ℤ) := by
  norm_num

theorem v7short_test_0048_conclusion : ∃ x y : ℤ, (-294 : ℤ) = (770 : ℤ) * x + (392 : ℤ) * y := by
  have hgcd : (Int.gcd (770 : ℤ) (392 : ℤ) : ℤ) = 14 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (770 : ℤ) (392 : ℤ) (-294 : ℤ)).2
  simpa [hgcd] using v7short_test_0048_divides

theorem v7short_test_0060_gcd : Nat.gcd 528 495 = 33 := by
  norm_num [Nat.gcd]

theorem v7short_test_0060_step_0 : (528 : ℤ) = 1 * 495 + 33 := by
  norm_num

theorem v7short_test_0060_step_1 : (495 : ℤ) = 15 * 33 + 0 := by
  norm_num

theorem v7short_test_0060_divides : (33 : ℤ) ∣ (-726 : ℤ) := by
  norm_num

theorem v7short_test_0060_conclusion : ∃ x y : ℤ, (-726 : ℤ) = (528 : ℤ) * x + (495 : ℤ) * y := by
  have hgcd : (Int.gcd (528 : ℤ) (495 : ℤ) : ℤ) = 33 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (528 : ℤ) (495 : ℤ) (-726 : ℤ)).2
  simpa [hgcd] using v7short_test_0060_divides

theorem v7short_test_0065_gcd : Nat.gcd 351 270 = 27 := by
  norm_num [Nat.gcd]

theorem v7short_test_0065_step_0 : (351 : ℤ) = 1 * 270 + 81 := by
  norm_num

theorem v7short_test_0065_step_1 : (270 : ℤ) = 3 * 81 + 27 := by
  norm_num

theorem v7short_test_0065_step_2 : (81 : ℤ) = 3 * 27 + 0 := by
  norm_num

theorem v7short_test_0065_divides : ¬ (27 : ℤ) ∣ (-403 : ℤ) := by
  norm_num

theorem v7short_test_0065_conclusion : ¬ (∃ x y : ℤ, (-403 : ℤ) = (351 : ℤ) * x + (270 : ℤ) * y) := by
  have hgcd : (Int.gcd (351 : ℤ) (270 : ℤ) : ℤ) = 27 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (351 : ℤ) (270 : ℤ) (-403 : ℤ)).1 h
  rw [hgcd] at hd
  exact v7short_test_0065_divides hd

theorem v7short_test_0067_gcd : Nat.gcd 155 630 = 5 := by
  norm_num [Nat.gcd]

theorem v7short_test_0067_step_0 : (630 : ℤ) = 4 * 155 + 10 := by
  norm_num

theorem v7short_test_0067_step_1 : (155 : ℤ) = 15 * 10 + 5 := by
  norm_num

theorem v7short_test_0067_step_2 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem v7short_test_0067_divides : ¬ (5 : ℤ) ∣ (-72 : ℤ) := by
  norm_num

theorem v7short_test_0067_conclusion : ¬ (∃ x y : ℤ, (-72 : ℤ) = (155 : ℤ) * x + (630 : ℤ) * y) := by
  have hgcd : (Int.gcd (155 : ℤ) (630 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (155 : ℤ) (630 : ℤ) (-72 : ℤ)).1 h
  rw [hgcd] at hd
  exact v7short_test_0067_divides hd

theorem v7short_test_0075_gcd : Nat.gcd 266 308 = 14 := by
  norm_num [Nat.gcd]

theorem v7short_test_0075_step_0 : (308 : ℤ) = 1 * 266 + 42 := by
  norm_num

theorem v7short_test_0075_step_1 : (266 : ℤ) = 6 * 42 + 14 := by
  norm_num

theorem v7short_test_0075_step_2 : (42 : ℤ) = 3 * 14 + 0 := by
  norm_num

theorem v7short_test_0075_divides : ¬ (14 : ℤ) ∣ (320 : ℤ) := by
  norm_num

theorem v7short_test_0075_conclusion : ¬ (∃ x y : ℤ, (320 : ℤ) = (266 : ℤ) * x + (308 : ℤ) * y) := by
  have hgcd : (Int.gcd (266 : ℤ) (308 : ℤ) : ℤ) = 14 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (266 : ℤ) (308 : ℤ) (320 : ℤ)).1 h
  rw [hgcd] at hd
  exact v7short_test_0075_divides hd

theorem v7short_test_0076_gcd : Nat.gcd 915 960 = 15 := by
  norm_num [Nat.gcd]

theorem v7short_test_0076_step_0 : (960 : ℤ) = 1 * 915 + 45 := by
  norm_num

theorem v7short_test_0076_step_1 : (915 : ℤ) = 20 * 45 + 15 := by
  norm_num

theorem v7short_test_0076_step_2 : (45 : ℤ) = 3 * 15 + 0 := by
  norm_num

theorem v7short_test_0076_divides : (15 : ℤ) ∣ (225 : ℤ) := by
  norm_num

theorem v7short_test_0076_conclusion : ∃ x y : ℤ, (225 : ℤ) = (915 : ℤ) * x + (960 : ℤ) * y := by
  have hgcd : (Int.gcd (915 : ℤ) (960 : ℤ) : ℤ) = 15 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (915 : ℤ) (960 : ℤ) (225 : ℤ)).2
  simpa [hgcd] using v7short_test_0076_divides

theorem v7short_test_0081_gcd : Nat.gcd 208 40 = 8 := by
  norm_num [Nat.gcd]

theorem v7short_test_0081_step_0 : (208 : ℤ) = 5 * 40 + 8 := by
  norm_num

theorem v7short_test_0081_step_1 : (40 : ℤ) = 5 * 8 + 0 := by
  norm_num

theorem v7short_test_0081_divides : ¬ (8 : ℤ) ∣ (-50 : ℤ) := by
  norm_num

theorem v7short_test_0081_conclusion : ¬ (∃ x y : ℤ, (-50 : ℤ) = (208 : ℤ) * x + (40 : ℤ) * y) := by
  have hgcd : (Int.gcd (208 : ℤ) (40 : ℤ) : ℤ) = 8 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (208 : ℤ) (40 : ℤ) (-50 : ℤ)).1 h
  rw [hgcd] at hd
  exact v7short_test_0081_divides hd

theorem v7short_test_0082_gcd : Nat.gcd 12 244 = 4 := by
  norm_num [Nat.gcd]

theorem v7short_test_0082_step_0 : (244 : ℤ) = 20 * 12 + 4 := by
  norm_num

theorem v7short_test_0082_step_1 : (12 : ℤ) = 3 * 4 + 0 := by
  norm_num

theorem v7short_test_0082_divides : (4 : ℤ) ∣ (-88 : ℤ) := by
  norm_num

theorem v7short_test_0082_conclusion : ∃ x y : ℤ, (-88 : ℤ) = (12 : ℤ) * x + (244 : ℤ) * y := by
  have hgcd : (Int.gcd (12 : ℤ) (244 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (12 : ℤ) (244 : ℤ) (-88 : ℤ)).2
  simpa [hgcd] using v7short_test_0082_divides

theorem v7short_test_0083_gcd : Nat.gcd 292 308 = 4 := by
  norm_num [Nat.gcd]

theorem v7short_test_0083_step_0 : (308 : ℤ) = 1 * 292 + 16 := by
  norm_num

theorem v7short_test_0083_step_1 : (292 : ℤ) = 18 * 16 + 4 := by
  norm_num

theorem v7short_test_0083_step_2 : (16 : ℤ) = 4 * 4 + 0 := by
  norm_num

theorem v7short_test_0083_divides : ¬ (4 : ℤ) ∣ (10 : ℤ) := by
  norm_num

theorem v7short_test_0083_conclusion : ¬ (∃ x y : ℤ, (10 : ℤ) = (292 : ℤ) * x + (308 : ℤ) * y) := by
  have hgcd : (Int.gcd (292 : ℤ) (308 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (292 : ℤ) (308 : ℤ) (10 : ℤ)).1 h
  rw [hgcd] at hd
  exact v7short_test_0083_divides hd

theorem v7short_test_0090_gcd : Nat.gcd 273 231 = 21 := by
  norm_num [Nat.gcd]

theorem v7short_test_0090_step_0 : (273 : ℤ) = 1 * 231 + 42 := by
  norm_num

theorem v7short_test_0090_step_1 : (231 : ℤ) = 5 * 42 + 21 := by
  norm_num

theorem v7short_test_0090_step_2 : (42 : ℤ) = 2 * 21 + 0 := by
  norm_num

theorem v7short_test_0090_divides : (21 : ℤ) ∣ (231 : ℤ) := by
  norm_num

theorem v7short_test_0090_conclusion : ∃ x y : ℤ, (231 : ℤ) = (273 : ℤ) * x + (231 : ℤ) * y := by
  have hgcd : (Int.gcd (273 : ℤ) (231 : ℤ) : ℤ) = 21 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (273 : ℤ) (231 : ℤ) (231 : ℤ)).2
  simpa [hgcd] using v7short_test_0090_divides

theorem v7short_test_0091_gcd : Nat.gcd 240 22 = 2 := by
  norm_num [Nat.gcd]

theorem v7short_test_0091_step_0 : (240 : ℤ) = 10 * 22 + 20 := by
  norm_num

theorem v7short_test_0091_step_1 : (22 : ℤ) = 1 * 20 + 2 := by
  norm_num

theorem v7short_test_0091_step_2 : (20 : ℤ) = 10 * 2 + 0 := by
  norm_num

theorem v7short_test_0091_divides : ¬ (2 : ℤ) ∣ (49 : ℤ) := by
  norm_num

theorem v7short_test_0091_conclusion : ¬ (∃ x y : ℤ, (49 : ℤ) = (240 : ℤ) * x + (22 : ℤ) * y) := by
  have hgcd : (Int.gcd (240 : ℤ) (22 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (240 : ℤ) (22 : ℤ) (49 : ℤ)).1 h
  rw [hgcd] at hd
  exact v7short_test_0091_divides hd

end AtomicClaimCertificates
