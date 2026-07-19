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

theorem v8long_test_0000_gcd : Nat.gcd 354 870 = 6 := by
  norm_num [Nat.gcd]

theorem v8long_test_0000_step_0 : (870 : ℤ) = 2 * 354 + 162 := by
  norm_num

theorem v8long_test_0000_step_1 : (354 : ℤ) = 2 * 162 + 30 := by
  norm_num

theorem v8long_test_0000_step_2 : (162 : ℤ) = 5 * 30 + 12 := by
  norm_num

theorem v8long_test_0000_step_3 : (30 : ℤ) = 2 * 12 + 6 := by
  norm_num

theorem v8long_test_0000_step_4 : (12 : ℤ) = 2 * 6 + 0 := by
  norm_num

theorem v8long_test_0000_divides : (6 : ℤ) ∣ (60 : ℤ) := by
  norm_num

theorem v8long_test_0000_conclusion : ∃ x y : ℤ, (60 : ℤ) = (354 : ℤ) * x + (870 : ℤ) * y := by
  have hgcd : (Int.gcd (354 : ℤ) (870 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (354 : ℤ) (870 : ℤ) (60 : ℤ)).2
  simpa [hgcd] using v8long_test_0000_divides

theorem v8long_test_0003_gcd : Nat.gcd 176 126 = 2 := by
  norm_num [Nat.gcd]

theorem v8long_test_0003_step_0 : (176 : ℤ) = 1 * 126 + 50 := by
  norm_num

theorem v8long_test_0003_step_1 : (126 : ℤ) = 2 * 50 + 26 := by
  norm_num

theorem v8long_test_0003_step_2 : (50 : ℤ) = 1 * 26 + 24 := by
  norm_num

theorem v8long_test_0003_step_3 : (26 : ℤ) = 1 * 24 + 2 := by
  norm_num

theorem v8long_test_0003_step_4 : (24 : ℤ) = 12 * 2 + 0 := by
  norm_num

theorem v8long_test_0003_divides : ¬ (2 : ℤ) ∣ (37 : ℤ) := by
  norm_num

theorem v8long_test_0003_conclusion : ¬ (∃ x y : ℤ, (37 : ℤ) = (176 : ℤ) * x + (126 : ℤ) * y) := by
  have hgcd : (Int.gcd (176 : ℤ) (126 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (176 : ℤ) (126 : ℤ) (37 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8long_test_0003_divides hd

theorem v8long_test_0006_gcd : Nat.gcd 384 294 = 6 := by
  norm_num [Nat.gcd]

theorem v8long_test_0006_step_0 : (384 : ℤ) = 1 * 294 + 90 := by
  norm_num

theorem v8long_test_0006_step_1 : (294 : ℤ) = 3 * 90 + 24 := by
  norm_num

theorem v8long_test_0006_step_2 : (90 : ℤ) = 3 * 24 + 18 := by
  norm_num

theorem v8long_test_0006_step_3 : (24 : ℤ) = 1 * 18 + 6 := by
  norm_num

theorem v8long_test_0006_step_4 : (18 : ℤ) = 3 * 6 + 0 := by
  norm_num

theorem v8long_test_0006_divides : (6 : ℤ) ∣ (6 : ℤ) := by
  norm_num

theorem v8long_test_0006_conclusion : ∃ x y : ℤ, (6 : ℤ) = (384 : ℤ) * x + (294 : ℤ) * y := by
  have hgcd : (Int.gcd (384 : ℤ) (294 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (384 : ℤ) (294 : ℤ) (6 : ℤ)).2
  simpa [hgcd] using v8long_test_0006_divides

theorem v8long_test_0011_gcd : Nat.gcd 273 511 = 7 := by
  norm_num [Nat.gcd]

theorem v8long_test_0011_step_0 : (511 : ℤ) = 1 * 273 + 238 := by
  norm_num

theorem v8long_test_0011_step_1 : (273 : ℤ) = 1 * 238 + 35 := by
  norm_num

theorem v8long_test_0011_step_2 : (238 : ℤ) = 6 * 35 + 28 := by
  norm_num

theorem v8long_test_0011_step_3 : (35 : ℤ) = 1 * 28 + 7 := by
  norm_num

theorem v8long_test_0011_step_4 : (28 : ℤ) = 4 * 7 + 0 := by
  norm_num

theorem v8long_test_0011_divides : ¬ (7 : ℤ) ∣ (-89 : ℤ) := by
  norm_num

theorem v8long_test_0011_conclusion : ¬ (∃ x y : ℤ, (-89 : ℤ) = (273 : ℤ) * x + (511 : ℤ) * y) := by
  have hgcd : (Int.gcd (273 : ℤ) (511 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (273 : ℤ) (511 : ℤ) (-89 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8long_test_0011_divides hd

theorem v8long_test_0019_gcd : Nat.gcd 505 640 = 5 := by
  norm_num [Nat.gcd]

theorem v8long_test_0019_step_0 : (640 : ℤ) = 1 * 505 + 135 := by
  norm_num

theorem v8long_test_0019_step_1 : (505 : ℤ) = 3 * 135 + 100 := by
  norm_num

theorem v8long_test_0019_step_2 : (135 : ℤ) = 1 * 100 + 35 := by
  norm_num

theorem v8long_test_0019_step_3 : (100 : ℤ) = 2 * 35 + 30 := by
  norm_num

theorem v8long_test_0019_step_4 : (35 : ℤ) = 1 * 30 + 5 := by
  norm_num

theorem v8long_test_0019_step_5 : (30 : ℤ) = 6 * 5 + 0 := by
  norm_num

theorem v8long_test_0019_divides : ¬ (5 : ℤ) ∣ (11 : ℤ) := by
  norm_num

theorem v8long_test_0019_conclusion : ¬ (∃ x y : ℤ, (11 : ℤ) = (505 : ℤ) * x + (640 : ℤ) * y) := by
  have hgcd : (Int.gcd (505 : ℤ) (640 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (505 : ℤ) (640 : ℤ) (11 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8long_test_0019_divides hd

theorem v8long_test_0020_gcd : Nat.gcd 336 180 = 12 := by
  norm_num [Nat.gcd]

theorem v8long_test_0020_step_0 : (336 : ℤ) = 1 * 180 + 156 := by
  norm_num

theorem v8long_test_0020_step_1 : (180 : ℤ) = 1 * 156 + 24 := by
  norm_num

theorem v8long_test_0020_step_2 : (156 : ℤ) = 6 * 24 + 12 := by
  norm_num

theorem v8long_test_0020_step_3 : (24 : ℤ) = 2 * 12 + 0 := by
  norm_num

theorem v8long_test_0020_divides : (12 : ℤ) ∣ (-156 : ℤ) := by
  norm_num

theorem v8long_test_0020_conclusion : ∃ x y : ℤ, (-156 : ℤ) = (336 : ℤ) * x + (180 : ℤ) * y := by
  have hgcd : (Int.gcd (336 : ℤ) (180 : ℤ) : ℤ) = 12 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (336 : ℤ) (180 : ℤ) (-156 : ℤ)).2
  simpa [hgcd] using v8long_test_0020_divides

theorem v8long_test_0023_gcd : Nat.gcd 262 354 = 2 := by
  norm_num [Nat.gcd]

theorem v8long_test_0023_step_0 : (354 : ℤ) = 1 * 262 + 92 := by
  norm_num

theorem v8long_test_0023_step_1 : (262 : ℤ) = 2 * 92 + 78 := by
  norm_num

theorem v8long_test_0023_step_2 : (92 : ℤ) = 1 * 78 + 14 := by
  norm_num

theorem v8long_test_0023_step_3 : (78 : ℤ) = 5 * 14 + 8 := by
  norm_num

theorem v8long_test_0023_step_4 : (14 : ℤ) = 1 * 8 + 6 := by
  norm_num

theorem v8long_test_0023_step_5 : (8 : ℤ) = 1 * 6 + 2 := by
  norm_num

theorem v8long_test_0023_step_6 : (6 : ℤ) = 3 * 2 + 0 := by
  norm_num

theorem v8long_test_0023_divides : ¬ (2 : ℤ) ∣ (-49 : ℤ) := by
  norm_num

theorem v8long_test_0023_conclusion : ¬ (∃ x y : ℤ, (-49 : ℤ) = (262 : ℤ) * x + (354 : ℤ) * y) := by
  have hgcd : (Int.gcd (262 : ℤ) (354 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (262 : ℤ) (354 : ℤ) (-49 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8long_test_0023_divides hd

theorem v8long_test_0028_gcd : Nat.gcd 873 450 = 9 := by
  norm_num [Nat.gcd]

theorem v8long_test_0028_step_0 : (873 : ℤ) = 1 * 450 + 423 := by
  norm_num

theorem v8long_test_0028_step_1 : (450 : ℤ) = 1 * 423 + 27 := by
  norm_num

theorem v8long_test_0028_step_2 : (423 : ℤ) = 15 * 27 + 18 := by
  norm_num

theorem v8long_test_0028_step_3 : (27 : ℤ) = 1 * 18 + 9 := by
  norm_num

theorem v8long_test_0028_step_4 : (18 : ℤ) = 2 * 9 + 0 := by
  norm_num

theorem v8long_test_0028_divides : (9 : ℤ) ∣ (-144 : ℤ) := by
  norm_num

theorem v8long_test_0028_conclusion : ∃ x y : ℤ, (-144 : ℤ) = (873 : ℤ) * x + (450 : ℤ) * y := by
  have hgcd : (Int.gcd (873 : ℤ) (450 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (873 : ℤ) (450 : ℤ) (-144 : ℤ)).2
  simpa [hgcd] using v8long_test_0028_divides

theorem v8long_test_0029_gcd : Nat.gcd 416 252 = 4 := by
  norm_num [Nat.gcd]

theorem v8long_test_0029_step_0 : (416 : ℤ) = 1 * 252 + 164 := by
  norm_num

theorem v8long_test_0029_step_1 : (252 : ℤ) = 1 * 164 + 88 := by
  norm_num

theorem v8long_test_0029_step_2 : (164 : ℤ) = 1 * 88 + 76 := by
  norm_num

theorem v8long_test_0029_step_3 : (88 : ℤ) = 1 * 76 + 12 := by
  norm_num

theorem v8long_test_0029_step_4 : (76 : ℤ) = 6 * 12 + 4 := by
  norm_num

theorem v8long_test_0029_step_5 : (12 : ℤ) = 3 * 4 + 0 := by
  norm_num

theorem v8long_test_0029_divides : ¬ (4 : ℤ) ∣ (50 : ℤ) := by
  norm_num

theorem v8long_test_0029_conclusion : ¬ (∃ x y : ℤ, (50 : ℤ) = (416 : ℤ) * x + (252 : ℤ) * y) := by
  have hgcd : (Int.gcd (416 : ℤ) (252 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (416 : ℤ) (252 : ℤ) (50 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8long_test_0029_divides hd

theorem v8long_test_0032_gcd : Nat.gcd 290 840 = 10 := by
  norm_num [Nat.gcd]

theorem v8long_test_0032_step_0 : (840 : ℤ) = 2 * 290 + 260 := by
  norm_num

theorem v8long_test_0032_step_1 : (290 : ℤ) = 1 * 260 + 30 := by
  norm_num

theorem v8long_test_0032_step_2 : (260 : ℤ) = 8 * 30 + 20 := by
  norm_num

theorem v8long_test_0032_step_3 : (30 : ℤ) = 1 * 20 + 10 := by
  norm_num

theorem v8long_test_0032_step_4 : (20 : ℤ) = 2 * 10 + 0 := by
  norm_num

theorem v8long_test_0032_divides : (10 : ℤ) ∣ (-100 : ℤ) := by
  norm_num

theorem v8long_test_0032_conclusion : ∃ x y : ℤ, (-100 : ℤ) = (290 : ℤ) * x + (840 : ℤ) * y := by
  have hgcd : (Int.gcd (290 : ℤ) (840 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (290 : ℤ) (840 : ℤ) (-100 : ℤ)).2
  simpa [hgcd] using v8long_test_0032_divides

theorem v8long_test_0033_gcd : Nat.gcd 494 190 = 38 := by
  norm_num [Nat.gcd]

theorem v8long_test_0033_step_0 : (494 : ℤ) = 2 * 190 + 114 := by
  norm_num

theorem v8long_test_0033_step_1 : (190 : ℤ) = 1 * 114 + 76 := by
  norm_num

theorem v8long_test_0033_step_2 : (114 : ℤ) = 1 * 76 + 38 := by
  norm_num

theorem v8long_test_0033_step_3 : (76 : ℤ) = 2 * 38 + 0 := by
  norm_num

theorem v8long_test_0033_divides : ¬ (38 : ℤ) ∣ (-86 : ℤ) := by
  norm_num

theorem v8long_test_0033_conclusion : ¬ (∃ x y : ℤ, (-86 : ℤ) = (494 : ℤ) * x + (190 : ℤ) * y) := by
  have hgcd : (Int.gcd (494 : ℤ) (190 : ℤ) : ℤ) = 38 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (494 : ℤ) (190 : ℤ) (-86 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8long_test_0033_divides hd

theorem v8long_test_0035_gcd : Nat.gcd 539 518 = 7 := by
  norm_num [Nat.gcd]

theorem v8long_test_0035_step_0 : (539 : ℤ) = 1 * 518 + 21 := by
  norm_num

theorem v8long_test_0035_step_1 : (518 : ℤ) = 24 * 21 + 14 := by
  norm_num

theorem v8long_test_0035_step_2 : (21 : ℤ) = 1 * 14 + 7 := by
  norm_num

theorem v8long_test_0035_step_3 : (14 : ℤ) = 2 * 7 + 0 := by
  norm_num

theorem v8long_test_0035_divides : ¬ (7 : ℤ) ∣ (-83 : ℤ) := by
  norm_num

theorem v8long_test_0035_conclusion : ¬ (∃ x y : ℤ, (-83 : ℤ) = (539 : ℤ) * x + (518 : ℤ) * y) := by
  have hgcd : (Int.gcd (539 : ℤ) (518 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (539 : ℤ) (518 : ℤ) (-83 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8long_test_0035_divides hd

theorem v8long_test_0036_gcd : Nat.gcd 117 309 = 3 := by
  norm_num [Nat.gcd]

theorem v8long_test_0036_step_0 : (309 : ℤ) = 2 * 117 + 75 := by
  norm_num

theorem v8long_test_0036_step_1 : (117 : ℤ) = 1 * 75 + 42 := by
  norm_num

theorem v8long_test_0036_step_2 : (75 : ℤ) = 1 * 42 + 33 := by
  norm_num

theorem v8long_test_0036_step_3 : (42 : ℤ) = 1 * 33 + 9 := by
  norm_num

theorem v8long_test_0036_step_4 : (33 : ℤ) = 3 * 9 + 6 := by
  norm_num

theorem v8long_test_0036_step_5 : (9 : ℤ) = 1 * 6 + 3 := by
  norm_num

theorem v8long_test_0036_step_6 : (6 : ℤ) = 2 * 3 + 0 := by
  norm_num

theorem v8long_test_0036_divides : (3 : ℤ) ∣ (48 : ℤ) := by
  norm_num

theorem v8long_test_0036_conclusion : ∃ x y : ℤ, (48 : ℤ) = (117 : ℤ) * x + (309 : ℤ) * y := by
  have hgcd : (Int.gcd (117 : ℤ) (309 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (117 : ℤ) (309 : ℤ) (48 : ℤ)).2
  simpa [hgcd] using v8long_test_0036_divides

theorem v8long_test_0041_gcd : Nat.gcd 278 374 = 2 := by
  norm_num [Nat.gcd]

theorem v8long_test_0041_step_0 : (374 : ℤ) = 1 * 278 + 96 := by
  norm_num

theorem v8long_test_0041_step_1 : (278 : ℤ) = 2 * 96 + 86 := by
  norm_num

theorem v8long_test_0041_step_2 : (96 : ℤ) = 1 * 86 + 10 := by
  norm_num

theorem v8long_test_0041_step_3 : (86 : ℤ) = 8 * 10 + 6 := by
  norm_num

theorem v8long_test_0041_step_4 : (10 : ℤ) = 1 * 6 + 4 := by
  norm_num

theorem v8long_test_0041_step_5 : (6 : ℤ) = 1 * 4 + 2 := by
  norm_num

theorem v8long_test_0041_step_6 : (4 : ℤ) = 2 * 2 + 0 := by
  norm_num

theorem v8long_test_0041_divides : ¬ (2 : ℤ) ∣ (13 : ℤ) := by
  norm_num

theorem v8long_test_0041_conclusion : ¬ (∃ x y : ℤ, (13 : ℤ) = (278 : ℤ) * x + (374 : ℤ) * y) := by
  have hgcd : (Int.gcd (278 : ℤ) (374 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (278 : ℤ) (374 : ℤ) (13 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8long_test_0041_divides hd

theorem v8long_test_0044_gcd : Nat.gcd 471 429 = 3 := by
  norm_num [Nat.gcd]

theorem v8long_test_0044_step_0 : (471 : ℤ) = 1 * 429 + 42 := by
  norm_num

theorem v8long_test_0044_step_1 : (429 : ℤ) = 10 * 42 + 9 := by
  norm_num

theorem v8long_test_0044_step_2 : (42 : ℤ) = 4 * 9 + 6 := by
  norm_num

theorem v8long_test_0044_step_3 : (9 : ℤ) = 1 * 6 + 3 := by
  norm_num

theorem v8long_test_0044_step_4 : (6 : ℤ) = 2 * 3 + 0 := by
  norm_num

theorem v8long_test_0044_divides : (3 : ℤ) ∣ (-42 : ℤ) := by
  norm_num

theorem v8long_test_0044_conclusion : ∃ x y : ℤ, (-42 : ℤ) = (471 : ℤ) * x + (429 : ℤ) * y := by
  have hgcd : (Int.gcd (471 : ℤ) (429 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (471 : ℤ) (429 : ℤ) (-42 : ℤ)).2
  simpa [hgcd] using v8long_test_0044_divides

theorem v8long_test_0045_gcd : Nat.gcd 300 170 = 10 := by
  norm_num [Nat.gcd]

theorem v8long_test_0045_step_0 : (300 : ℤ) = 1 * 170 + 130 := by
  norm_num

theorem v8long_test_0045_step_1 : (170 : ℤ) = 1 * 130 + 40 := by
  norm_num

theorem v8long_test_0045_step_2 : (130 : ℤ) = 3 * 40 + 10 := by
  norm_num

theorem v8long_test_0045_step_3 : (40 : ℤ) = 4 * 10 + 0 := by
  norm_num

theorem v8long_test_0045_divides : ¬ (10 : ℤ) ∣ (-244 : ℤ) := by
  norm_num

theorem v8long_test_0045_conclusion : ¬ (∃ x y : ℤ, (-244 : ℤ) = (300 : ℤ) * x + (170 : ℤ) * y) := by
  have hgcd : (Int.gcd (300 : ℤ) (170 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (300 : ℤ) (170 : ℤ) (-244 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8long_test_0045_divides hd

theorem v8long_test_0052_gcd : Nat.gcd 325 620 = 5 := by
  norm_num [Nat.gcd]

theorem v8long_test_0052_step_0 : (620 : ℤ) = 1 * 325 + 295 := by
  norm_num

theorem v8long_test_0052_step_1 : (325 : ℤ) = 1 * 295 + 30 := by
  norm_num

theorem v8long_test_0052_step_2 : (295 : ℤ) = 9 * 30 + 25 := by
  norm_num

theorem v8long_test_0052_step_3 : (30 : ℤ) = 1 * 25 + 5 := by
  norm_num

theorem v8long_test_0052_step_4 : (25 : ℤ) = 5 * 5 + 0 := by
  norm_num

theorem v8long_test_0052_divides : (5 : ℤ) ∣ (10 : ℤ) := by
  norm_num

theorem v8long_test_0052_conclusion : ∃ x y : ℤ, (10 : ℤ) = (325 : ℤ) * x + (620 : ℤ) * y := by
  have hgcd : (Int.gcd (325 : ℤ) (620 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (325 : ℤ) (620 : ℤ) (10 : ℤ)).2
  simpa [hgcd] using v8long_test_0052_divides

theorem v8long_test_0053_gcd : Nat.gcd 395 500 = 5 := by
  norm_num [Nat.gcd]

theorem v8long_test_0053_step_0 : (500 : ℤ) = 1 * 395 + 105 := by
  norm_num

theorem v8long_test_0053_step_1 : (395 : ℤ) = 3 * 105 + 80 := by
  norm_num

theorem v8long_test_0053_step_2 : (105 : ℤ) = 1 * 80 + 25 := by
  norm_num

theorem v8long_test_0053_step_3 : (80 : ℤ) = 3 * 25 + 5 := by
  norm_num

theorem v8long_test_0053_step_4 : (25 : ℤ) = 5 * 5 + 0 := by
  norm_num

theorem v8long_test_0053_divides : ¬ (5 : ℤ) ∣ (-122 : ℤ) := by
  norm_num

theorem v8long_test_0053_conclusion : ¬ (∃ x y : ℤ, (-122 : ℤ) = (395 : ℤ) * x + (500 : ℤ) * y) := by
  have hgcd : (Int.gcd (395 : ℤ) (500 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (395 : ℤ) (500 : ℤ) (-122 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8long_test_0053_divides hd

theorem v8long_test_0054_gcd : Nat.gcd 292 306 = 2 := by
  norm_num [Nat.gcd]

theorem v8long_test_0054_step_0 : (306 : ℤ) = 1 * 292 + 14 := by
  norm_num

theorem v8long_test_0054_step_1 : (292 : ℤ) = 20 * 14 + 12 := by
  norm_num

theorem v8long_test_0054_step_2 : (14 : ℤ) = 1 * 12 + 2 := by
  norm_num

theorem v8long_test_0054_step_3 : (12 : ℤ) = 6 * 2 + 0 := by
  norm_num

theorem v8long_test_0054_divides : (2 : ℤ) ∣ (44 : ℤ) := by
  norm_num

theorem v8long_test_0054_conclusion : ∃ x y : ℤ, (44 : ℤ) = (292 : ℤ) * x + (306 : ℤ) * y := by
  have hgcd : (Int.gcd (292 : ℤ) (306 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (292 : ℤ) (306 : ℤ) (44 : ℤ)).2
  simpa [hgcd] using v8long_test_0054_divides

theorem v8long_test_0055_gcd : Nat.gcd 588 903 = 21 := by
  norm_num [Nat.gcd]

theorem v8long_test_0055_step_0 : (903 : ℤ) = 1 * 588 + 315 := by
  norm_num

theorem v8long_test_0055_step_1 : (588 : ℤ) = 1 * 315 + 273 := by
  norm_num

theorem v8long_test_0055_step_2 : (315 : ℤ) = 1 * 273 + 42 := by
  norm_num

theorem v8long_test_0055_step_3 : (273 : ℤ) = 6 * 42 + 21 := by
  norm_num

theorem v8long_test_0055_step_4 : (42 : ℤ) = 2 * 21 + 0 := by
  norm_num

theorem v8long_test_0055_divides : ¬ (21 : ℤ) ∣ (-71 : ℤ) := by
  norm_num

theorem v8long_test_0055_conclusion : ¬ (∃ x y : ℤ, (-71 : ℤ) = (588 : ℤ) * x + (903 : ℤ) * y) := by
  have hgcd : (Int.gcd (588 : ℤ) (903 : ℤ) : ℤ) = 21 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (588 : ℤ) (903 : ℤ) (-71 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8long_test_0055_divides hd

theorem v8long_test_0058_gcd : Nat.gcd 414 489 = 3 := by
  norm_num [Nat.gcd]

theorem v8long_test_0058_step_0 : (489 : ℤ) = 1 * 414 + 75 := by
  norm_num

theorem v8long_test_0058_step_1 : (414 : ℤ) = 5 * 75 + 39 := by
  norm_num

theorem v8long_test_0058_step_2 : (75 : ℤ) = 1 * 39 + 36 := by
  norm_num

theorem v8long_test_0058_step_3 : (39 : ℤ) = 1 * 36 + 3 := by
  norm_num

theorem v8long_test_0058_step_4 : (36 : ℤ) = 12 * 3 + 0 := by
  norm_num

theorem v8long_test_0058_divides : (3 : ℤ) ∣ (48 : ℤ) := by
  norm_num

theorem v8long_test_0058_conclusion : ∃ x y : ℤ, (48 : ℤ) = (414 : ℤ) * x + (489 : ℤ) * y := by
  have hgcd : (Int.gcd (414 : ℤ) (489 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (414 : ℤ) (489 : ℤ) (48 : ℤ)).2
  simpa [hgcd] using v8long_test_0058_divides

theorem v8long_test_0062_gcd : Nat.gcd 200 148 = 4 := by
  norm_num [Nat.gcd]

theorem v8long_test_0062_step_0 : (200 : ℤ) = 1 * 148 + 52 := by
  norm_num

theorem v8long_test_0062_step_1 : (148 : ℤ) = 2 * 52 + 44 := by
  norm_num

theorem v8long_test_0062_step_2 : (52 : ℤ) = 1 * 44 + 8 := by
  norm_num

theorem v8long_test_0062_step_3 : (44 : ℤ) = 5 * 8 + 4 := by
  norm_num

theorem v8long_test_0062_step_4 : (8 : ℤ) = 2 * 4 + 0 := by
  norm_num

theorem v8long_test_0062_divides : (4 : ℤ) ∣ (48 : ℤ) := by
  norm_num

theorem v8long_test_0062_conclusion : ∃ x y : ℤ, (48 : ℤ) = (200 : ℤ) * x + (148 : ℤ) * y := by
  have hgcd : (Int.gcd (200 : ℤ) (148 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (200 : ℤ) (148 : ℤ) (48 : ℤ)).2
  simpa [hgcd] using v8long_test_0062_divides

theorem v8long_test_0064_gcd : Nat.gcd 492 336 = 12 := by
  norm_num [Nat.gcd]

theorem v8long_test_0064_step_0 : (492 : ℤ) = 1 * 336 + 156 := by
  norm_num

theorem v8long_test_0064_step_1 : (336 : ℤ) = 2 * 156 + 24 := by
  norm_num

theorem v8long_test_0064_step_2 : (156 : ℤ) = 6 * 24 + 12 := by
  norm_num

theorem v8long_test_0064_step_3 : (24 : ℤ) = 2 * 12 + 0 := by
  norm_num

theorem v8long_test_0064_divides : (12 : ℤ) ∣ (-204 : ℤ) := by
  norm_num

theorem v8long_test_0064_conclusion : ∃ x y : ℤ, (-204 : ℤ) = (492 : ℤ) * x + (336 : ℤ) * y := by
  have hgcd : (Int.gcd (492 : ℤ) (336 : ℤ) : ℤ) = 12 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (492 : ℤ) (336 : ℤ) (-204 : ℤ)).2
  simpa [hgcd] using v8long_test_0064_divides

theorem v8long_test_0065_gcd : Nat.gcd 465 160 = 5 := by
  norm_num [Nat.gcd]

theorem v8long_test_0065_step_0 : (465 : ℤ) = 2 * 160 + 145 := by
  norm_num

theorem v8long_test_0065_step_1 : (160 : ℤ) = 1 * 145 + 15 := by
  norm_num

theorem v8long_test_0065_step_2 : (145 : ℤ) = 9 * 15 + 10 := by
  norm_num

theorem v8long_test_0065_step_3 : (15 : ℤ) = 1 * 10 + 5 := by
  norm_num

theorem v8long_test_0065_step_4 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem v8long_test_0065_divides : ¬ (5 : ℤ) ∣ (-41 : ℤ) := by
  norm_num

theorem v8long_test_0065_conclusion : ¬ (∃ x y : ℤ, (-41 : ℤ) = (465 : ℤ) * x + (160 : ℤ) * y) := by
  have hgcd : (Int.gcd (465 : ℤ) (160 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (465 : ℤ) (160 : ℤ) (-41 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8long_test_0065_divides hd

theorem v8long_test_0069_gcd : Nat.gcd 119 217 = 7 := by
  norm_num [Nat.gcd]

theorem v8long_test_0069_step_0 : (217 : ℤ) = 1 * 119 + 98 := by
  norm_num

theorem v8long_test_0069_step_1 : (119 : ℤ) = 1 * 98 + 21 := by
  norm_num

theorem v8long_test_0069_step_2 : (98 : ℤ) = 4 * 21 + 14 := by
  norm_num

theorem v8long_test_0069_step_3 : (21 : ℤ) = 1 * 14 + 7 := by
  norm_num

theorem v8long_test_0069_step_4 : (14 : ℤ) = 2 * 7 + 0 := by
  norm_num

theorem v8long_test_0069_divides : ¬ (7 : ℤ) ∣ (137 : ℤ) := by
  norm_num

theorem v8long_test_0069_conclusion : ¬ (∃ x y : ℤ, (137 : ℤ) = (119 : ℤ) * x + (217 : ℤ) * y) := by
  have hgcd : (Int.gcd (119 : ℤ) (217 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (119 : ℤ) (217 : ℤ) (137 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8long_test_0069_divides hd

theorem v8long_test_0071_gcd : Nat.gcd 168 190 = 2 := by
  norm_num [Nat.gcd]

theorem v8long_test_0071_step_0 : (190 : ℤ) = 1 * 168 + 22 := by
  norm_num

theorem v8long_test_0071_step_1 : (168 : ℤ) = 7 * 22 + 14 := by
  norm_num

theorem v8long_test_0071_step_2 : (22 : ℤ) = 1 * 14 + 8 := by
  norm_num

theorem v8long_test_0071_step_3 : (14 : ℤ) = 1 * 8 + 6 := by
  norm_num

theorem v8long_test_0071_step_4 : (8 : ℤ) = 1 * 6 + 2 := by
  norm_num

theorem v8long_test_0071_step_5 : (6 : ℤ) = 3 * 2 + 0 := by
  norm_num

theorem v8long_test_0071_divides : ¬ (2 : ℤ) ∣ (25 : ℤ) := by
  norm_num

theorem v8long_test_0071_conclusion : ¬ (∃ x y : ℤ, (25 : ℤ) = (168 : ℤ) * x + (190 : ℤ) * y) := by
  have hgcd : (Int.gcd (168 : ℤ) (190 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (168 : ℤ) (190 : ℤ) (25 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8long_test_0071_divides hd

theorem v8long_test_0072_gcd : Nat.gcd 230 405 = 5 := by
  norm_num [Nat.gcd]

theorem v8long_test_0072_step_0 : (405 : ℤ) = 1 * 230 + 175 := by
  norm_num

theorem v8long_test_0072_step_1 : (230 : ℤ) = 1 * 175 + 55 := by
  norm_num

theorem v8long_test_0072_step_2 : (175 : ℤ) = 3 * 55 + 10 := by
  norm_num

theorem v8long_test_0072_step_3 : (55 : ℤ) = 5 * 10 + 5 := by
  norm_num

theorem v8long_test_0072_step_4 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem v8long_test_0072_divides : (5 : ℤ) ∣ (-105 : ℤ) := by
  norm_num

theorem v8long_test_0072_conclusion : ∃ x y : ℤ, (-105 : ℤ) = (230 : ℤ) * x + (405 : ℤ) * y := by
  have hgcd : (Int.gcd (230 : ℤ) (405 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (230 : ℤ) (405 : ℤ) (-105 : ℤ)).2
  simpa [hgcd] using v8long_test_0072_divides

theorem v8long_test_0075_gcd : Nat.gcd 884 546 = 26 := by
  norm_num [Nat.gcd]

theorem v8long_test_0075_step_0 : (884 : ℤ) = 1 * 546 + 338 := by
  norm_num

theorem v8long_test_0075_step_1 : (546 : ℤ) = 1 * 338 + 208 := by
  norm_num

theorem v8long_test_0075_step_2 : (338 : ℤ) = 1 * 208 + 130 := by
  norm_num

theorem v8long_test_0075_step_3 : (208 : ℤ) = 1 * 130 + 78 := by
  norm_num

theorem v8long_test_0075_step_4 : (130 : ℤ) = 1 * 78 + 52 := by
  norm_num

theorem v8long_test_0075_step_5 : (78 : ℤ) = 1 * 52 + 26 := by
  norm_num

theorem v8long_test_0075_step_6 : (52 : ℤ) = 2 * 26 + 0 := by
  norm_num

theorem v8long_test_0075_divides : ¬ (26 : ℤ) ∣ (541 : ℤ) := by
  norm_num

theorem v8long_test_0075_conclusion : ¬ (∃ x y : ℤ, (541 : ℤ) = (884 : ℤ) * x + (546 : ℤ) * y) := by
  have hgcd : (Int.gcd (884 : ℤ) (546 : ℤ) : ℤ) = 26 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (884 : ℤ) (546 : ℤ) (541 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8long_test_0075_divides hd

theorem v8long_test_0078_gcd : Nat.gcd 867 323 = 17 := by
  norm_num [Nat.gcd]

theorem v8long_test_0078_step_0 : (867 : ℤ) = 2 * 323 + 221 := by
  norm_num

theorem v8long_test_0078_step_1 : (323 : ℤ) = 1 * 221 + 102 := by
  norm_num

theorem v8long_test_0078_step_2 : (221 : ℤ) = 2 * 102 + 17 := by
  norm_num

theorem v8long_test_0078_step_3 : (102 : ℤ) = 6 * 17 + 0 := by
  norm_num

theorem v8long_test_0078_divides : (17 : ℤ) ∣ (221 : ℤ) := by
  norm_num

theorem v8long_test_0078_conclusion : ∃ x y : ℤ, (221 : ℤ) = (867 : ℤ) * x + (323 : ℤ) * y := by
  have hgcd : (Int.gcd (867 : ℤ) (323 : ℤ) : ℤ) = 17 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (867 : ℤ) (323 : ℤ) (221 : ℤ)).2
  simpa [hgcd] using v8long_test_0078_divides

theorem v8long_test_0080_gcd : Nat.gcd 390 155 = 5 := by
  norm_num [Nat.gcd]

theorem v8long_test_0080_step_0 : (390 : ℤ) = 2 * 155 + 80 := by
  norm_num

theorem v8long_test_0080_step_1 : (155 : ℤ) = 1 * 80 + 75 := by
  norm_num

theorem v8long_test_0080_step_2 : (80 : ℤ) = 1 * 75 + 5 := by
  norm_num

theorem v8long_test_0080_step_3 : (75 : ℤ) = 15 * 5 + 0 := by
  norm_num

theorem v8long_test_0080_divides : (5 : ℤ) ∣ (70 : ℤ) := by
  norm_num

theorem v8long_test_0080_conclusion : ∃ x y : ℤ, (70 : ℤ) = (390 : ℤ) * x + (155 : ℤ) * y := by
  have hgcd : (Int.gcd (390 : ℤ) (155 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (390 : ℤ) (155 : ℤ) (70 : ℤ)).2
  simpa [hgcd] using v8long_test_0080_divides

theorem v8long_test_0083_gcd : Nat.gcd 978 648 = 6 := by
  norm_num [Nat.gcd]

theorem v8long_test_0083_step_0 : (978 : ℤ) = 1 * 648 + 330 := by
  norm_num

theorem v8long_test_0083_step_1 : (648 : ℤ) = 1 * 330 + 318 := by
  norm_num

theorem v8long_test_0083_step_2 : (330 : ℤ) = 1 * 318 + 12 := by
  norm_num

theorem v8long_test_0083_step_3 : (318 : ℤ) = 26 * 12 + 6 := by
  norm_num

theorem v8long_test_0083_step_4 : (12 : ℤ) = 2 * 6 + 0 := by
  norm_num

theorem v8long_test_0083_divides : ¬ (6 : ℤ) ∣ (-4 : ℤ) := by
  norm_num

theorem v8long_test_0083_conclusion : ¬ (∃ x y : ℤ, (-4 : ℤ) = (978 : ℤ) * x + (648 : ℤ) * y) := by
  have hgcd : (Int.gcd (978 : ℤ) (648 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (978 : ℤ) (648 : ℤ) (-4 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8long_test_0083_divides hd

theorem v8long_test_0085_gcd : Nat.gcd 775 410 = 5 := by
  norm_num [Nat.gcd]

theorem v8long_test_0085_step_0 : (775 : ℤ) = 1 * 410 + 365 := by
  norm_num

theorem v8long_test_0085_step_1 : (410 : ℤ) = 1 * 365 + 45 := by
  norm_num

theorem v8long_test_0085_step_2 : (365 : ℤ) = 8 * 45 + 5 := by
  norm_num

theorem v8long_test_0085_step_3 : (45 : ℤ) = 9 * 5 + 0 := by
  norm_num

theorem v8long_test_0085_divides : ¬ (5 : ℤ) ∣ (64 : ℤ) := by
  norm_num

theorem v8long_test_0085_conclusion : ¬ (∃ x y : ℤ, (64 : ℤ) = (775 : ℤ) * x + (410 : ℤ) * y) := by
  have hgcd : (Int.gcd (775 : ℤ) (410 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (775 : ℤ) (410 : ℤ) (64 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8long_test_0085_divides hd

theorem v8long_test_0088_gcd : Nat.gcd 680 630 = 10 := by
  norm_num [Nat.gcd]

theorem v8long_test_0088_step_0 : (680 : ℤ) = 1 * 630 + 50 := by
  norm_num

theorem v8long_test_0088_step_1 : (630 : ℤ) = 12 * 50 + 30 := by
  norm_num

theorem v8long_test_0088_step_2 : (50 : ℤ) = 1 * 30 + 20 := by
  norm_num

theorem v8long_test_0088_step_3 : (30 : ℤ) = 1 * 20 + 10 := by
  norm_num

theorem v8long_test_0088_step_4 : (20 : ℤ) = 2 * 10 + 0 := by
  norm_num

theorem v8long_test_0088_divides : (10 : ℤ) ∣ (-250 : ℤ) := by
  norm_num

theorem v8long_test_0088_conclusion : ∃ x y : ℤ, (-250 : ℤ) = (680 : ℤ) * x + (630 : ℤ) * y := by
  have hgcd : (Int.gcd (680 : ℤ) (630 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (680 : ℤ) (630 : ℤ) (-250 : ℤ)).2
  simpa [hgcd] using v8long_test_0088_divides

theorem v8long_test_0096_gcd : Nat.gcd 228 558 = 6 := by
  norm_num [Nat.gcd]

theorem v8long_test_0096_step_0 : (558 : ℤ) = 2 * 228 + 102 := by
  norm_num

theorem v8long_test_0096_step_1 : (228 : ℤ) = 2 * 102 + 24 := by
  norm_num

theorem v8long_test_0096_step_2 : (102 : ℤ) = 4 * 24 + 6 := by
  norm_num

theorem v8long_test_0096_step_3 : (24 : ℤ) = 4 * 6 + 0 := by
  norm_num

theorem v8long_test_0096_divides : (6 : ℤ) ∣ (-24 : ℤ) := by
  norm_num

theorem v8long_test_0096_conclusion : ∃ x y : ℤ, (-24 : ℤ) = (228 : ℤ) * x + (558 : ℤ) * y := by
  have hgcd : (Int.gcd (228 : ℤ) (558 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (228 : ℤ) (558 : ℤ) (-24 : ℤ)).2
  simpa [hgcd] using v8long_test_0096_divides

theorem v8short_test_0000_gcd : Nat.gcd 45 132 = 3 := by
  norm_num [Nat.gcd]

theorem v8short_test_0000_step_0 : (132 : ℤ) = 2 * 45 + 42 := by
  norm_num

theorem v8short_test_0000_step_1 : (45 : ℤ) = 1 * 42 + 3 := by
  norm_num

theorem v8short_test_0000_step_2 : (42 : ℤ) = 14 * 3 + 0 := by
  norm_num

theorem v8short_test_0000_divides : (3 : ℤ) ∣ (36 : ℤ) := by
  norm_num

theorem v8short_test_0000_conclusion : ∃ x y : ℤ, (36 : ℤ) = (45 : ℤ) * x + (132 : ℤ) * y := by
  have hgcd : (Int.gcd (45 : ℤ) (132 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (45 : ℤ) (132 : ℤ) (36 : ℤ)).2
  simpa [hgcd] using v8short_test_0000_divides

theorem v8short_test_0001_gcd : Nat.gcd 210 36 = 6 := by
  norm_num [Nat.gcd]

theorem v8short_test_0001_step_0 : (210 : ℤ) = 5 * 36 + 30 := by
  norm_num

theorem v8short_test_0001_step_1 : (36 : ℤ) = 1 * 30 + 6 := by
  norm_num

theorem v8short_test_0001_step_2 : (30 : ℤ) = 5 * 6 + 0 := by
  norm_num

theorem v8short_test_0001_divides : ¬ (6 : ℤ) ∣ (-15 : ℤ) := by
  norm_num

theorem v8short_test_0001_conclusion : ¬ (∃ x y : ℤ, (-15 : ℤ) = (210 : ℤ) * x + (36 : ℤ) * y) := by
  have hgcd : (Int.gcd (210 : ℤ) (36 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (210 : ℤ) (36 : ℤ) (-15 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8short_test_0001_divides hd

theorem v8short_test_0008_gcd : Nat.gcd 105 45 = 15 := by
  norm_num [Nat.gcd]

theorem v8short_test_0008_step_0 : (105 : ℤ) = 2 * 45 + 15 := by
  norm_num

theorem v8short_test_0008_step_1 : (45 : ℤ) = 3 * 15 + 0 := by
  norm_num

theorem v8short_test_0008_divides : (15 : ℤ) ∣ (-360 : ℤ) := by
  norm_num

theorem v8short_test_0008_conclusion : ∃ x y : ℤ, (-360 : ℤ) = (105 : ℤ) * x + (45 : ℤ) * y := by
  have hgcd : (Int.gcd (105 : ℤ) (45 : ℤ) : ℤ) = 15 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (105 : ℤ) (45 : ℤ) (-360 : ℤ)).2
  simpa [hgcd] using v8short_test_0008_divides

theorem v8short_test_0011_gcd : Nat.gcd 762 90 = 6 := by
  norm_num [Nat.gcd]

theorem v8short_test_0011_step_0 : (762 : ℤ) = 8 * 90 + 42 := by
  norm_num

theorem v8short_test_0011_step_1 : (90 : ℤ) = 2 * 42 + 6 := by
  norm_num

theorem v8short_test_0011_step_2 : (42 : ℤ) = 7 * 6 + 0 := by
  norm_num

theorem v8short_test_0011_divides : ¬ (6 : ℤ) ∣ (-59 : ℤ) := by
  norm_num

theorem v8short_test_0011_conclusion : ¬ (∃ x y : ℤ, (-59 : ℤ) = (762 : ℤ) * x + (90 : ℤ) * y) := by
  have hgcd : (Int.gcd (762 : ℤ) (90 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (762 : ℤ) (90 : ℤ) (-59 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8short_test_0011_divides hd

theorem v8short_test_0018_gcd : Nat.gcd 415 405 = 5 := by
  norm_num [Nat.gcd]

theorem v8short_test_0018_step_0 : (415 : ℤ) = 1 * 405 + 10 := by
  norm_num

theorem v8short_test_0018_step_1 : (405 : ℤ) = 40 * 10 + 5 := by
  norm_num

theorem v8short_test_0018_step_2 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem v8short_test_0018_divides : (5 : ℤ) ∣ (-40 : ℤ) := by
  norm_num

theorem v8short_test_0018_conclusion : ∃ x y : ℤ, (-40 : ℤ) = (415 : ℤ) * x + (405 : ℤ) * y := by
  have hgcd : (Int.gcd (415 : ℤ) (405 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (415 : ℤ) (405 : ℤ) (-40 : ℤ)).2
  simpa [hgcd] using v8short_test_0018_divides

theorem v8short_test_0026_gcd : Nat.gcd 332 18 = 2 := by
  norm_num [Nat.gcd]

theorem v8short_test_0026_step_0 : (332 : ℤ) = 18 * 18 + 8 := by
  norm_num

theorem v8short_test_0026_step_1 : (18 : ℤ) = 2 * 8 + 2 := by
  norm_num

theorem v8short_test_0026_step_2 : (8 : ℤ) = 4 * 2 + 0 := by
  norm_num

theorem v8short_test_0026_divides : (2 : ℤ) ∣ (4 : ℤ) := by
  norm_num

theorem v8short_test_0026_conclusion : ∃ x y : ℤ, (4 : ℤ) = (332 : ℤ) * x + (18 : ℤ) * y := by
  have hgcd : (Int.gcd (332 : ℤ) (18 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (332 : ℤ) (18 : ℤ) (4 : ℤ)).2
  simpa [hgcd] using v8short_test_0026_divides

theorem v8short_test_0034_gcd : Nat.gcd 700 695 = 5 := by
  norm_num [Nat.gcd]

theorem v8short_test_0034_step_0 : (700 : ℤ) = 1 * 695 + 5 := by
  norm_num

theorem v8short_test_0034_step_1 : (695 : ℤ) = 139 * 5 + 0 := by
  norm_num

theorem v8short_test_0034_divides : (5 : ℤ) ∣ (45 : ℤ) := by
  norm_num

theorem v8short_test_0034_conclusion : ∃ x y : ℤ, (45 : ℤ) = (700 : ℤ) * x + (695 : ℤ) * y := by
  have hgcd : (Int.gcd (700 : ℤ) (695 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (700 : ℤ) (695 : ℤ) (45 : ℤ)).2
  simpa [hgcd] using v8short_test_0034_divides

theorem v8short_test_0035_gcd : Nat.gcd 126 231 = 21 := by
  norm_num [Nat.gcd]

theorem v8short_test_0035_step_0 : (231 : ℤ) = 1 * 126 + 105 := by
  norm_num

theorem v8short_test_0035_step_1 : (126 : ℤ) = 1 * 105 + 21 := by
  norm_num

theorem v8short_test_0035_step_2 : (105 : ℤ) = 5 * 21 + 0 := by
  norm_num

theorem v8short_test_0035_divides : ¬ (21 : ℤ) ∣ (-148 : ℤ) := by
  norm_num

theorem v8short_test_0035_conclusion : ¬ (∃ x y : ℤ, (-148 : ℤ) = (126 : ℤ) * x + (231 : ℤ) * y) := by
  have hgcd : (Int.gcd (126 : ℤ) (231 : ℤ) : ℤ) = 21 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (126 : ℤ) (231 : ℤ) (-148 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8short_test_0035_divides hd

theorem v8short_test_0037_gcd : Nat.gcd 735 795 = 15 := by
  norm_num [Nat.gcd]

theorem v8short_test_0037_step_0 : (795 : ℤ) = 1 * 735 + 60 := by
  norm_num

theorem v8short_test_0037_step_1 : (735 : ℤ) = 12 * 60 + 15 := by
  norm_num

theorem v8short_test_0037_step_2 : (60 : ℤ) = 4 * 15 + 0 := by
  norm_num

theorem v8short_test_0037_divides : ¬ (15 : ℤ) ∣ (-341 : ℤ) := by
  norm_num

theorem v8short_test_0037_conclusion : ¬ (∃ x y : ℤ, (-341 : ℤ) = (735 : ℤ) * x + (795 : ℤ) * y) := by
  have hgcd : (Int.gcd (735 : ℤ) (795 : ℤ) : ℤ) = 15 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (735 : ℤ) (795 : ℤ) (-341 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8short_test_0037_divides hd

theorem v8short_test_0042_gcd : Nat.gcd 234 81 = 9 := by
  norm_num [Nat.gcd]

theorem v8short_test_0042_step_0 : (234 : ℤ) = 2 * 81 + 72 := by
  norm_num

theorem v8short_test_0042_step_1 : (81 : ℤ) = 1 * 72 + 9 := by
  norm_num

theorem v8short_test_0042_step_2 : (72 : ℤ) = 8 * 9 + 0 := by
  norm_num

theorem v8short_test_0042_divides : (9 : ℤ) ∣ (-162 : ℤ) := by
  norm_num

theorem v8short_test_0042_conclusion : ∃ x y : ℤ, (-162 : ℤ) = (234 : ℤ) * x + (81 : ℤ) * y := by
  have hgcd : (Int.gcd (234 : ℤ) (81 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (234 : ℤ) (81 : ℤ) (-162 : ℤ)).2
  simpa [hgcd] using v8short_test_0042_divides

theorem v8short_test_0045_gcd : Nat.gcd 147 219 = 3 := by
  norm_num [Nat.gcd]

theorem v8short_test_0045_step_0 : (219 : ℤ) = 1 * 147 + 72 := by
  norm_num

theorem v8short_test_0045_step_1 : (147 : ℤ) = 2 * 72 + 3 := by
  norm_num

theorem v8short_test_0045_step_2 : (72 : ℤ) = 24 * 3 + 0 := by
  norm_num

theorem v8short_test_0045_divides : ¬ (3 : ℤ) ∣ (-73 : ℤ) := by
  norm_num

theorem v8short_test_0045_conclusion : ¬ (∃ x y : ℤ, (-73 : ℤ) = (147 : ℤ) * x + (219 : ℤ) * y) := by
  have hgcd : (Int.gcd (147 : ℤ) (219 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (147 : ℤ) (219 : ℤ) (-73 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8short_test_0045_divides hd

theorem v8short_test_0048_gcd : Nat.gcd 18 93 = 3 := by
  norm_num [Nat.gcd]

theorem v8short_test_0048_step_0 : (93 : ℤ) = 5 * 18 + 3 := by
  norm_num

theorem v8short_test_0048_step_1 : (18 : ℤ) = 6 * 3 + 0 := by
  norm_num

theorem v8short_test_0048_divides : (3 : ℤ) ∣ (63 : ℤ) := by
  norm_num

theorem v8short_test_0048_conclusion : ∃ x y : ℤ, (63 : ℤ) = (18 : ℤ) * x + (93 : ℤ) * y := by
  have hgcd : (Int.gcd (18 : ℤ) (93 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (18 : ℤ) (93 : ℤ) (63 : ℤ)).2
  simpa [hgcd] using v8short_test_0048_divides

theorem v8short_test_0049_gcd : Nat.gcd 260 515 = 5 := by
  norm_num [Nat.gcd]

theorem v8short_test_0049_step_0 : (515 : ℤ) = 1 * 260 + 255 := by
  norm_num

theorem v8short_test_0049_step_1 : (260 : ℤ) = 1 * 255 + 5 := by
  norm_num

theorem v8short_test_0049_step_2 : (255 : ℤ) = 51 * 5 + 0 := by
  norm_num

theorem v8short_test_0049_divides : ¬ (5 : ℤ) ∣ (-91 : ℤ) := by
  norm_num

theorem v8short_test_0049_conclusion : ¬ (∃ x y : ℤ, (-91 : ℤ) = (260 : ℤ) * x + (515 : ℤ) * y) := by
  have hgcd : (Int.gcd (260 : ℤ) (515 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (260 : ℤ) (515 : ℤ) (-91 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8short_test_0049_divides hd

theorem v8short_test_0065_gcd : Nat.gcd 575 150 = 25 := by
  norm_num [Nat.gcd]

theorem v8short_test_0065_step_0 : (575 : ℤ) = 3 * 150 + 125 := by
  norm_num

theorem v8short_test_0065_step_1 : (150 : ℤ) = 1 * 125 + 25 := by
  norm_num

theorem v8short_test_0065_step_2 : (125 : ℤ) = 5 * 25 + 0 := by
  norm_num

theorem v8short_test_0065_divides : ¬ (25 : ℤ) ∣ (226 : ℤ) := by
  norm_num

theorem v8short_test_0065_conclusion : ¬ (∃ x y : ℤ, (226 : ℤ) = (575 : ℤ) * x + (150 : ℤ) * y) := by
  have hgcd : (Int.gcd (575 : ℤ) (150 : ℤ) : ℤ) = 25 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (575 : ℤ) (150 : ℤ) (226 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8short_test_0065_divides hd

theorem v8short_test_0066_gcd : Nat.gcd 210 250 = 10 := by
  norm_num [Nat.gcd]

theorem v8short_test_0066_step_0 : (250 : ℤ) = 1 * 210 + 40 := by
  norm_num

theorem v8short_test_0066_step_1 : (210 : ℤ) = 5 * 40 + 10 := by
  norm_num

theorem v8short_test_0066_step_2 : (40 : ℤ) = 4 * 10 + 0 := by
  norm_num

theorem v8short_test_0066_divides : (10 : ℤ) ∣ (30 : ℤ) := by
  norm_num

theorem v8short_test_0066_conclusion : ∃ x y : ℤ, (30 : ℤ) = (210 : ℤ) * x + (250 : ℤ) * y := by
  have hgcd : (Int.gcd (210 : ℤ) (250 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (210 : ℤ) (250 : ℤ) (30 : ℤ)).2
  simpa [hgcd] using v8short_test_0066_divides

theorem v8short_test_0068_gcd : Nat.gcd 91 497 = 7 := by
  norm_num [Nat.gcd]

theorem v8short_test_0068_step_0 : (497 : ℤ) = 5 * 91 + 42 := by
  norm_num

theorem v8short_test_0068_step_1 : (91 : ℤ) = 2 * 42 + 7 := by
  norm_num

theorem v8short_test_0068_step_2 : (42 : ℤ) = 6 * 7 + 0 := by
  norm_num

theorem v8short_test_0068_divides : (7 : ℤ) ∣ (28 : ℤ) := by
  norm_num

theorem v8short_test_0068_conclusion : ∃ x y : ℤ, (28 : ℤ) = (91 : ℤ) * x + (497 : ℤ) * y := by
  have hgcd : (Int.gcd (91 : ℤ) (497 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (91 : ℤ) (497 : ℤ) (28 : ℤ)).2
  simpa [hgcd] using v8short_test_0068_divides

theorem v8short_test_0076_gcd : Nat.gcd 615 60 = 15 := by
  norm_num [Nat.gcd]

theorem v8short_test_0076_step_0 : (615 : ℤ) = 10 * 60 + 15 := by
  norm_num

theorem v8short_test_0076_step_1 : (60 : ℤ) = 4 * 15 + 0 := by
  norm_num

theorem v8short_test_0076_divides : (15 : ℤ) ∣ (195 : ℤ) := by
  norm_num

theorem v8short_test_0076_conclusion : ∃ x y : ℤ, (195 : ℤ) = (615 : ℤ) * x + (60 : ℤ) * y := by
  have hgcd : (Int.gcd (615 : ℤ) (60 : ℤ) : ℤ) = 15 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (615 : ℤ) (60 : ℤ) (195 : ℤ)).2
  simpa [hgcd] using v8short_test_0076_divides

theorem v8short_test_0080_gcd : Nat.gcd 165 370 = 5 := by
  norm_num [Nat.gcd]

theorem v8short_test_0080_step_0 : (370 : ℤ) = 2 * 165 + 40 := by
  norm_num

theorem v8short_test_0080_step_1 : (165 : ℤ) = 4 * 40 + 5 := by
  norm_num

theorem v8short_test_0080_step_2 : (40 : ℤ) = 8 * 5 + 0 := by
  norm_num

theorem v8short_test_0080_divides : (5 : ℤ) ∣ (-40 : ℤ) := by
  norm_num

theorem v8short_test_0080_conclusion : ∃ x y : ℤ, (-40 : ℤ) = (165 : ℤ) * x + (370 : ℤ) * y := by
  have hgcd : (Int.gcd (165 : ℤ) (370 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (165 : ℤ) (370 : ℤ) (-40 : ℤ)).2
  simpa [hgcd] using v8short_test_0080_divides

theorem v8short_test_0084_gcd : Nat.gcd 660 225 = 15 := by
  norm_num [Nat.gcd]

theorem v8short_test_0084_step_0 : (660 : ℤ) = 2 * 225 + 210 := by
  norm_num

theorem v8short_test_0084_step_1 : (225 : ℤ) = 1 * 210 + 15 := by
  norm_num

theorem v8short_test_0084_step_2 : (210 : ℤ) = 14 * 15 + 0 := by
  norm_num

theorem v8short_test_0084_divides : (15 : ℤ) ∣ (-45 : ℤ) := by
  norm_num

theorem v8short_test_0084_conclusion : ∃ x y : ℤ, (-45 : ℤ) = (660 : ℤ) * x + (225 : ℤ) * y := by
  have hgcd : (Int.gcd (660 : ℤ) (225 : ℤ) : ℤ) = 15 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (660 : ℤ) (225 : ℤ) (-45 : ℤ)).2
  simpa [hgcd] using v8short_test_0084_divides

theorem v8short_test_0085_gcd : Nat.gcd 510 498 = 6 := by
  norm_num [Nat.gcd]

theorem v8short_test_0085_step_0 : (510 : ℤ) = 1 * 498 + 12 := by
  norm_num

theorem v8short_test_0085_step_1 : (498 : ℤ) = 41 * 12 + 6 := by
  norm_num

theorem v8short_test_0085_step_2 : (12 : ℤ) = 2 * 6 + 0 := by
  norm_num

theorem v8short_test_0085_divides : ¬ (6 : ℤ) ∣ (-76 : ℤ) := by
  norm_num

theorem v8short_test_0085_conclusion : ¬ (∃ x y : ℤ, (-76 : ℤ) = (510 : ℤ) * x + (498 : ℤ) * y) := by
  have hgcd : (Int.gcd (510 : ℤ) (498 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (510 : ℤ) (498 : ℤ) (-76 : ℤ)).1 h
  rw [hgcd] at hd
  exact v8short_test_0085_divides hd

end AtomicClaimCertificates
