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

theorem scale500_test_0012_gcd : Nat.gcd 453 276 = 3 := by
  norm_num [Nat.gcd]

theorem scale500_test_0012_step_0 : (453 : ℤ) = 1 * 276 + 177 := by
  norm_num

theorem scale500_test_0012_step_1 : (276 : ℤ) = 1 * 177 + 99 := by
  norm_num

theorem scale500_test_0012_step_2 : (177 : ℤ) = 1 * 99 + 78 := by
  norm_num

theorem scale500_test_0012_step_3 : (99 : ℤ) = 1 * 78 + 21 := by
  norm_num

theorem scale500_test_0012_step_4 : (78 : ℤ) = 3 * 21 + 15 := by
  norm_num

theorem scale500_test_0012_step_5 : (21 : ℤ) = 1 * 15 + 6 := by
  norm_num

theorem scale500_test_0012_step_6 : (15 : ℤ) = 2 * 6 + 3 := by
  norm_num

theorem scale500_test_0012_step_7 : (6 : ℤ) = 2 * 3 + 0 := by
  norm_num

theorem scale500_test_0012_divides : (3 : ℤ) ∣ (-75 : ℤ) := by
  norm_num

theorem scale500_test_0012_conclusion : ∃ x y : ℤ, (-75 : ℤ) = (453 : ℤ) * x + (276 : ℤ) * y := by
  have hgcd : (Int.gcd (453 : ℤ) (276 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (453 : ℤ) (276 : ℤ) (-75 : ℤ)).2
  simpa [hgcd] using scale500_test_0012_divides

theorem scale500_test_0015_gcd : Nat.gcd 350 332 = 2 := by
  norm_num [Nat.gcd]

theorem scale500_test_0015_step_0 : (350 : ℤ) = 1 * 332 + 18 := by
  norm_num

theorem scale500_test_0015_step_1 : (332 : ℤ) = 18 * 18 + 8 := by
  norm_num

theorem scale500_test_0015_step_2 : (18 : ℤ) = 2 * 8 + 2 := by
  norm_num

theorem scale500_test_0015_step_3 : (8 : ℤ) = 4 * 2 + 0 := by
  norm_num

theorem scale500_test_0015_divides : ¬ (2 : ℤ) ∣ (-27 : ℤ) := by
  norm_num

theorem scale500_test_0015_conclusion : ¬ (∃ x y : ℤ, (-27 : ℤ) = (350 : ℤ) * x + (332 : ℤ) * y) := by
  have hgcd : (Int.gcd (350 : ℤ) (332 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (350 : ℤ) (332 : ℤ) (-27 : ℤ)).1 h
  rw [hgcd] at hd
  exact scale500_test_0015_divides hd

theorem scale500_test_0019_gcd : Nat.gcd 235 170 = 5 := by
  norm_num [Nat.gcd]

theorem scale500_test_0019_step_0 : (235 : ℤ) = 1 * 170 + 65 := by
  norm_num

theorem scale500_test_0019_step_1 : (170 : ℤ) = 2 * 65 + 40 := by
  norm_num

theorem scale500_test_0019_step_2 : (65 : ℤ) = 1 * 40 + 25 := by
  norm_num

theorem scale500_test_0019_step_3 : (40 : ℤ) = 1 * 25 + 15 := by
  norm_num

theorem scale500_test_0019_step_4 : (25 : ℤ) = 1 * 15 + 10 := by
  norm_num

theorem scale500_test_0019_step_5 : (15 : ℤ) = 1 * 10 + 5 := by
  norm_num

theorem scale500_test_0019_step_6 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem scale500_test_0019_divides : ¬ (5 : ℤ) ∣ (124 : ℤ) := by
  norm_num

theorem scale500_test_0019_conclusion : ¬ (∃ x y : ℤ, (124 : ℤ) = (235 : ℤ) * x + (170 : ℤ) * y) := by
  have hgcd : (Int.gcd (235 : ℤ) (170 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (235 : ℤ) (170 : ℤ) (124 : ℤ)).1 h
  rw [hgcd] at hd
  exact scale500_test_0019_divides hd

theorem scale500_test_0020_gcd : Nat.gcd 302 306 = 2 := by
  norm_num [Nat.gcd]

theorem scale500_test_0020_step_0 : (306 : ℤ) = 1 * 302 + 4 := by
  norm_num

theorem scale500_test_0020_step_1 : (302 : ℤ) = 75 * 4 + 2 := by
  norm_num

theorem scale500_test_0020_step_2 : (4 : ℤ) = 2 * 2 + 0 := by
  norm_num

theorem scale500_test_0020_divides : (2 : ℤ) ∣ (-50 : ℤ) := by
  norm_num

theorem scale500_test_0020_conclusion : ∃ x y : ℤ, (-50 : ℤ) = (302 : ℤ) * x + (306 : ℤ) * y := by
  have hgcd : (Int.gcd (302 : ℤ) (306 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (302 : ℤ) (306 : ℤ) (-50 : ℤ)).2
  simpa [hgcd] using scale500_test_0020_divides

theorem scale500_test_0024_gcd : Nat.gcd 294 122 = 2 := by
  norm_num [Nat.gcd]

theorem scale500_test_0024_step_0 : (294 : ℤ) = 2 * 122 + 50 := by
  norm_num

theorem scale500_test_0024_step_1 : (122 : ℤ) = 2 * 50 + 22 := by
  norm_num

theorem scale500_test_0024_step_2 : (50 : ℤ) = 2 * 22 + 6 := by
  norm_num

theorem scale500_test_0024_step_3 : (22 : ℤ) = 3 * 6 + 4 := by
  norm_num

theorem scale500_test_0024_step_4 : (6 : ℤ) = 1 * 4 + 2 := by
  norm_num

theorem scale500_test_0024_step_5 : (4 : ℤ) = 2 * 2 + 0 := by
  norm_num

theorem scale500_test_0024_divides : (2 : ℤ) ∣ (-28 : ℤ) := by
  norm_num

theorem scale500_test_0024_conclusion : ∃ x y : ℤ, (-28 : ℤ) = (294 : ℤ) * x + (122 : ℤ) * y := by
  have hgcd : (Int.gcd (294 : ℤ) (122 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (294 : ℤ) (122 : ℤ) (-28 : ℤ)).2
  simpa [hgcd] using scale500_test_0024_divides

theorem scale500_test_0031_gcd : Nat.gcd 238 128 = 2 := by
  norm_num [Nat.gcd]

theorem scale500_test_0031_step_0 : (238 : ℤ) = 1 * 128 + 110 := by
  norm_num

theorem scale500_test_0031_step_1 : (128 : ℤ) = 1 * 110 + 18 := by
  norm_num

theorem scale500_test_0031_step_2 : (110 : ℤ) = 6 * 18 + 2 := by
  norm_num

theorem scale500_test_0031_step_3 : (18 : ℤ) = 9 * 2 + 0 := by
  norm_num

theorem scale500_test_0031_divides : ¬ (2 : ℤ) ∣ (9 : ℤ) := by
  norm_num

theorem scale500_test_0031_conclusion : ¬ (∃ x y : ℤ, (9 : ℤ) = (238 : ℤ) * x + (128 : ℤ) * y) := by
  have hgcd : (Int.gcd (238 : ℤ) (128 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (238 : ℤ) (128 : ℤ) (9 : ℤ)).1 h
  rw [hgcd] at hd
  exact scale500_test_0031_divides hd

theorem scale500_test_0036_gcd : Nat.gcd 244 16 = 4 := by
  norm_num [Nat.gcd]

theorem scale500_test_0036_step_0 : (244 : ℤ) = 15 * 16 + 4 := by
  norm_num

theorem scale500_test_0036_step_1 : (16 : ℤ) = 4 * 4 + 0 := by
  norm_num

theorem scale500_test_0036_divides : (4 : ℤ) ∣ (-32 : ℤ) := by
  norm_num

theorem scale500_test_0036_conclusion : ∃ x y : ℤ, (-32 : ℤ) = (244 : ℤ) * x + (16 : ℤ) * y := by
  have hgcd : (Int.gcd (244 : ℤ) (16 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (244 : ℤ) (16 : ℤ) (-32 : ℤ)).2
  simpa [hgcd] using scale500_test_0036_divides

theorem scale500_test_0040_gcd : Nat.gcd 336 90 = 6 := by
  norm_num [Nat.gcd]

theorem scale500_test_0040_step_0 : (336 : ℤ) = 3 * 90 + 66 := by
  norm_num

theorem scale500_test_0040_step_1 : (90 : ℤ) = 1 * 66 + 24 := by
  norm_num

theorem scale500_test_0040_step_2 : (66 : ℤ) = 2 * 24 + 18 := by
  norm_num

theorem scale500_test_0040_step_3 : (24 : ℤ) = 1 * 18 + 6 := by
  norm_num

theorem scale500_test_0040_step_4 : (18 : ℤ) = 3 * 6 + 0 := by
  norm_num

theorem scale500_test_0040_divides : (6 : ℤ) ∣ (-108 : ℤ) := by
  norm_num

theorem scale500_test_0040_conclusion : ∃ x y : ℤ, (-108 : ℤ) = (336 : ℤ) * x + (90 : ℤ) * y := by
  have hgcd : (Int.gcd (336 : ℤ) (90 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (336 : ℤ) (90 : ℤ) (-108 : ℤ)).2
  simpa [hgcd] using scale500_test_0040_divides

theorem scale500_test_0041_gcd : Nat.gcd 399 112 = 7 := by
  norm_num [Nat.gcd]

theorem scale500_test_0041_step_0 : (399 : ℤ) = 3 * 112 + 63 := by
  norm_num

theorem scale500_test_0041_step_1 : (112 : ℤ) = 1 * 63 + 49 := by
  norm_num

theorem scale500_test_0041_step_2 : (63 : ℤ) = 1 * 49 + 14 := by
  norm_num

theorem scale500_test_0041_step_3 : (49 : ℤ) = 3 * 14 + 7 := by
  norm_num

theorem scale500_test_0041_step_4 : (14 : ℤ) = 2 * 7 + 0 := by
  norm_num

theorem scale500_test_0041_divides : ¬ (7 : ℤ) ∣ (139 : ℤ) := by
  norm_num

theorem scale500_test_0041_conclusion : ¬ (∃ x y : ℤ, (139 : ℤ) = (399 : ℤ) * x + (112 : ℤ) * y) := by
  have hgcd : (Int.gcd (399 : ℤ) (112 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (399 : ℤ) (112 : ℤ) (139 : ℤ)).1 h
  rw [hgcd] at hd
  exact scale500_test_0041_divides hd

theorem scale500_test_0043_gcd : Nat.gcd 350 371 = 7 := by
  norm_num [Nat.gcd]

theorem scale500_test_0043_step_0 : (371 : ℤ) = 1 * 350 + 21 := by
  norm_num

theorem scale500_test_0043_step_1 : (350 : ℤ) = 16 * 21 + 14 := by
  norm_num

theorem scale500_test_0043_step_2 : (21 : ℤ) = 1 * 14 + 7 := by
  norm_num

theorem scale500_test_0043_step_3 : (14 : ℤ) = 2 * 7 + 0 := by
  norm_num

theorem scale500_test_0043_divides : ¬ (7 : ℤ) ∣ (31 : ℤ) := by
  norm_num

theorem scale500_test_0043_conclusion : ¬ (∃ x y : ℤ, (31 : ℤ) = (350 : ℤ) * x + (371 : ℤ) * y) := by
  have hgcd : (Int.gcd (350 : ℤ) (371 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (350 : ℤ) (371 : ℤ) (31 : ℤ)).1 h
  rw [hgcd] at hd
  exact scale500_test_0043_divides hd

theorem scale500_test_0044_gcd : Nat.gcd 278 302 = 2 := by
  norm_num [Nat.gcd]

theorem scale500_test_0044_step_0 : (302 : ℤ) = 1 * 278 + 24 := by
  norm_num

theorem scale500_test_0044_step_1 : (278 : ℤ) = 11 * 24 + 14 := by
  norm_num

theorem scale500_test_0044_step_2 : (24 : ℤ) = 1 * 14 + 10 := by
  norm_num

theorem scale500_test_0044_step_3 : (14 : ℤ) = 1 * 10 + 4 := by
  norm_num

theorem scale500_test_0044_step_4 : (10 : ℤ) = 2 * 4 + 2 := by
  norm_num

theorem scale500_test_0044_step_5 : (4 : ℤ) = 2 * 2 + 0 := by
  norm_num

theorem scale500_test_0044_divides : (2 : ℤ) ∣ (16 : ℤ) := by
  norm_num

theorem scale500_test_0044_conclusion : ∃ x y : ℤ, (16 : ℤ) = (278 : ℤ) * x + (302 : ℤ) * y := by
  have hgcd : (Int.gcd (278 : ℤ) (302 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (278 : ℤ) (302 : ℤ) (16 : ℤ)).2
  simpa [hgcd] using scale500_test_0044_divides

theorem scale500_test_0054_gcd : Nat.gcd 355 340 = 5 := by
  norm_num [Nat.gcd]

theorem scale500_test_0054_step_0 : (355 : ℤ) = 1 * 340 + 15 := by
  norm_num

theorem scale500_test_0054_step_1 : (340 : ℤ) = 22 * 15 + 10 := by
  norm_num

theorem scale500_test_0054_step_2 : (15 : ℤ) = 1 * 10 + 5 := by
  norm_num

theorem scale500_test_0054_step_3 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem scale500_test_0054_divides : (5 : ℤ) ∣ (-60 : ℤ) := by
  norm_num

theorem scale500_test_0054_conclusion : ∃ x y : ℤ, (-60 : ℤ) = (355 : ℤ) * x + (340 : ℤ) * y := by
  have hgcd : (Int.gcd (355 : ℤ) (340 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (355 : ℤ) (340 : ℤ) (-60 : ℤ)).2
  simpa [hgcd] using scale500_test_0054_divides

theorem scale500_test_0060_gcd : Nat.gcd 278 200 = 2 := by
  norm_num [Nat.gcd]

theorem scale500_test_0060_step_0 : (278 : ℤ) = 1 * 200 + 78 := by
  norm_num

theorem scale500_test_0060_step_1 : (200 : ℤ) = 2 * 78 + 44 := by
  norm_num

theorem scale500_test_0060_step_2 : (78 : ℤ) = 1 * 44 + 34 := by
  norm_num

theorem scale500_test_0060_step_3 : (44 : ℤ) = 1 * 34 + 10 := by
  norm_num

theorem scale500_test_0060_step_4 : (34 : ℤ) = 3 * 10 + 4 := by
  norm_num

theorem scale500_test_0060_step_5 : (10 : ℤ) = 2 * 4 + 2 := by
  norm_num

theorem scale500_test_0060_step_6 : (4 : ℤ) = 2 * 2 + 0 := by
  norm_num

theorem scale500_test_0060_divides : (2 : ℤ) ∣ (-36 : ℤ) := by
  norm_num

theorem scale500_test_0060_conclusion : ∃ x y : ℤ, (-36 : ℤ) = (278 : ℤ) * x + (200 : ℤ) * y := by
  have hgcd : (Int.gcd (278 : ℤ) (200 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (278 : ℤ) (200 : ℤ) (-36 : ℤ)).2
  simpa [hgcd] using scale500_test_0060_divides

theorem scale500_test_0062_gcd : Nat.gcd 326 136 = 2 := by
  norm_num [Nat.gcd]

theorem scale500_test_0062_step_0 : (326 : ℤ) = 2 * 136 + 54 := by
  norm_num

theorem scale500_test_0062_step_1 : (136 : ℤ) = 2 * 54 + 28 := by
  norm_num

theorem scale500_test_0062_step_2 : (54 : ℤ) = 1 * 28 + 26 := by
  norm_num

theorem scale500_test_0062_step_3 : (28 : ℤ) = 1 * 26 + 2 := by
  norm_num

theorem scale500_test_0062_step_4 : (26 : ℤ) = 13 * 2 + 0 := by
  norm_num

theorem scale500_test_0062_divides : (2 : ℤ) ∣ (-20 : ℤ) := by
  norm_num

theorem scale500_test_0062_conclusion : ∃ x y : ℤ, (-20 : ℤ) = (326 : ℤ) * x + (136 : ℤ) * y := by
  have hgcd : (Int.gcd (326 : ℤ) (136 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (326 : ℤ) (136 : ℤ) (-20 : ℤ)).2
  simpa [hgcd] using scale500_test_0062_divides

theorem scale500_test_0064_gcd : Nat.gcd 258 92 = 2 := by
  norm_num [Nat.gcd]

theorem scale500_test_0064_step_0 : (258 : ℤ) = 2 * 92 + 74 := by
  norm_num

theorem scale500_test_0064_step_1 : (92 : ℤ) = 1 * 74 + 18 := by
  norm_num

theorem scale500_test_0064_step_2 : (74 : ℤ) = 4 * 18 + 2 := by
  norm_num

theorem scale500_test_0064_step_3 : (18 : ℤ) = 9 * 2 + 0 := by
  norm_num

theorem scale500_test_0064_divides : (2 : ℤ) ∣ (-4 : ℤ) := by
  norm_num

theorem scale500_test_0064_conclusion : ∃ x y : ℤ, (-4 : ℤ) = (258 : ℤ) * x + (92 : ℤ) * y := by
  have hgcd : (Int.gcd (258 : ℤ) (92 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (258 : ℤ) (92 : ℤ) (-4 : ℤ)).2
  simpa [hgcd] using scale500_test_0064_divides

theorem scale500_test_0079_gcd : Nat.gcd 286 252 = 2 := by
  norm_num [Nat.gcd]

theorem scale500_test_0079_step_0 : (286 : ℤ) = 1 * 252 + 34 := by
  norm_num

theorem scale500_test_0079_step_1 : (252 : ℤ) = 7 * 34 + 14 := by
  norm_num

theorem scale500_test_0079_step_2 : (34 : ℤ) = 2 * 14 + 6 := by
  norm_num

theorem scale500_test_0079_step_3 : (14 : ℤ) = 2 * 6 + 2 := by
  norm_num

theorem scale500_test_0079_step_4 : (6 : ℤ) = 3 * 2 + 0 := by
  norm_num

theorem scale500_test_0079_divides : ¬ (2 : ℤ) ∣ (-13 : ℤ) := by
  norm_num

theorem scale500_test_0079_conclusion : ¬ (∃ x y : ℤ, (-13 : ℤ) = (286 : ℤ) * x + (252 : ℤ) * y) := by
  have hgcd : (Int.gcd (286 : ℤ) (252 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (286 : ℤ) (252 : ℤ) (-13 : ℤ)).1 h
  rw [hgcd] at hd
  exact scale500_test_0079_divides hd

end AtomicClaimCertificates
