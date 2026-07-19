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

theorem v9long_test_0000_gcd : Nat.gcd 897 667 = 23 := by
  norm_num [Nat.gcd]

theorem v9long_test_0000_step_0 : (897 : ℤ) = 1 * 667 + 230 := by
  norm_num

theorem v9long_test_0000_step_1 : (667 : ℤ) = 2 * 230 + 207 := by
  norm_num

theorem v9long_test_0000_step_2 : (230 : ℤ) = 1 * 207 + 23 := by
  norm_num

theorem v9long_test_0000_step_3 : (207 : ℤ) = 9 * 23 + 0 := by
  norm_num

theorem v9long_test_0000_divides : (23 : ℤ) ∣ (-437 : ℤ) := by
  norm_num

theorem v9long_test_0000_conclusion : ∃ x y : ℤ, (-437 : ℤ) = (897 : ℤ) * x + (667 : ℤ) * y := by
  have hgcd : (Int.gcd (897 : ℤ) (667 : ℤ) : ℤ) = 23 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (897 : ℤ) (667 : ℤ) (-437 : ℤ)).2
  simpa [hgcd] using v9long_test_0000_divides

theorem v9long_test_0012_gcd : Nat.gcd 420 264 = 12 := by
  norm_num [Nat.gcd]

theorem v9long_test_0012_step_0 : (420 : ℤ) = 1 * 264 + 156 := by
  norm_num

theorem v9long_test_0012_step_1 : (264 : ℤ) = 1 * 156 + 108 := by
  norm_num

theorem v9long_test_0012_step_2 : (156 : ℤ) = 1 * 108 + 48 := by
  norm_num

theorem v9long_test_0012_step_3 : (108 : ℤ) = 2 * 48 + 12 := by
  norm_num

theorem v9long_test_0012_step_4 : (48 : ℤ) = 4 * 12 + 0 := by
  norm_num

theorem v9long_test_0012_divides : (12 : ℤ) ∣ (-252 : ℤ) := by
  norm_num

theorem v9long_test_0012_conclusion : ∃ x y : ℤ, (-252 : ℤ) = (420 : ℤ) * x + (264 : ℤ) * y := by
  have hgcd : (Int.gcd (420 : ℤ) (264 : ℤ) : ℤ) = 12 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (420 : ℤ) (264 : ℤ) (-252 : ℤ)).2
  simpa [hgcd] using v9long_test_0012_divides

theorem v9long_test_0017_gcd : Nat.gcd 370 595 = 5 := by
  norm_num [Nat.gcd]

theorem v9long_test_0017_step_0 : (595 : ℤ) = 1 * 370 + 225 := by
  norm_num

theorem v9long_test_0017_step_1 : (370 : ℤ) = 1 * 225 + 145 := by
  norm_num

theorem v9long_test_0017_step_2 : (225 : ℤ) = 1 * 145 + 80 := by
  norm_num

theorem v9long_test_0017_step_3 : (145 : ℤ) = 1 * 80 + 65 := by
  norm_num

theorem v9long_test_0017_step_4 : (80 : ℤ) = 1 * 65 + 15 := by
  norm_num

theorem v9long_test_0017_step_5 : (65 : ℤ) = 4 * 15 + 5 := by
  norm_num

theorem v9long_test_0017_step_6 : (15 : ℤ) = 3 * 5 + 0 := by
  norm_num

theorem v9long_test_0017_divides : ¬ (5 : ℤ) ∣ (-17 : ℤ) := by
  norm_num

theorem v9long_test_0017_conclusion : ¬ (∃ x y : ℤ, (-17 : ℤ) = (370 : ℤ) * x + (595 : ℤ) * y) := by
  have hgcd : (Int.gcd (370 : ℤ) (595 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (370 : ℤ) (595 : ℤ) (-17 : ℤ)).1 h
  rw [hgcd] at hd
  exact v9long_test_0017_divides hd

theorem v9long_test_0019_gcd : Nat.gcd 580 890 = 10 := by
  norm_num [Nat.gcd]

theorem v9long_test_0019_step_0 : (890 : ℤ) = 1 * 580 + 310 := by
  norm_num

theorem v9long_test_0019_step_1 : (580 : ℤ) = 1 * 310 + 270 := by
  norm_num

theorem v9long_test_0019_step_2 : (310 : ℤ) = 1 * 270 + 40 := by
  norm_num

theorem v9long_test_0019_step_3 : (270 : ℤ) = 6 * 40 + 30 := by
  norm_num

theorem v9long_test_0019_step_4 : (40 : ℤ) = 1 * 30 + 10 := by
  norm_num

theorem v9long_test_0019_step_5 : (30 : ℤ) = 3 * 10 + 0 := by
  norm_num

theorem v9long_test_0019_divides : ¬ (10 : ℤ) ∣ (39 : ℤ) := by
  norm_num

theorem v9long_test_0019_conclusion : ¬ (∃ x y : ℤ, (39 : ℤ) = (580 : ℤ) * x + (890 : ℤ) * y) := by
  have hgcd : (Int.gcd (580 : ℤ) (890 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (580 : ℤ) (890 : ℤ) (39 : ℤ)).1 h
  rw [hgcd] at hd
  exact v9long_test_0019_divides hd

theorem v9long_test_0024_gcd : Nat.gcd 325 220 = 5 := by
  norm_num [Nat.gcd]

theorem v9long_test_0024_step_0 : (325 : ℤ) = 1 * 220 + 105 := by
  norm_num

theorem v9long_test_0024_step_1 : (220 : ℤ) = 2 * 105 + 10 := by
  norm_num

theorem v9long_test_0024_step_2 : (105 : ℤ) = 10 * 10 + 5 := by
  norm_num

theorem v9long_test_0024_step_3 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem v9long_test_0024_divides : (5 : ℤ) ∣ (-85 : ℤ) := by
  norm_num

theorem v9long_test_0024_conclusion : ∃ x y : ℤ, (-85 : ℤ) = (325 : ℤ) * x + (220 : ℤ) * y := by
  have hgcd : (Int.gcd (325 : ℤ) (220 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (325 : ℤ) (220 : ℤ) (-85 : ℤ)).2
  simpa [hgcd] using v9long_test_0024_divides

theorem v9long_test_0025_gcd : Nat.gcd 536 344 = 8 := by
  norm_num [Nat.gcd]

theorem v9long_test_0025_step_0 : (536 : ℤ) = 1 * 344 + 192 := by
  norm_num

theorem v9long_test_0025_step_1 : (344 : ℤ) = 1 * 192 + 152 := by
  norm_num

theorem v9long_test_0025_step_2 : (192 : ℤ) = 1 * 152 + 40 := by
  norm_num

theorem v9long_test_0025_step_3 : (152 : ℤ) = 3 * 40 + 32 := by
  norm_num

theorem v9long_test_0025_step_4 : (40 : ℤ) = 1 * 32 + 8 := by
  norm_num

theorem v9long_test_0025_step_5 : (32 : ℤ) = 4 * 8 + 0 := by
  norm_num

theorem v9long_test_0025_divides : ¬ (8 : ℤ) ∣ (-105 : ℤ) := by
  norm_num

theorem v9long_test_0025_conclusion : ¬ (∃ x y : ℤ, (-105 : ℤ) = (536 : ℤ) * x + (344 : ℤ) * y) := by
  have hgcd : (Int.gcd (536 : ℤ) (344 : ℤ) : ℤ) = 8 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (536 : ℤ) (344 : ℤ) (-105 : ℤ)).1 h
  rw [hgcd] at hd
  exact v9long_test_0025_divides hd

theorem v9long_test_0027_gcd : Nat.gcd 510 774 = 6 := by
  norm_num [Nat.gcd]

theorem v9long_test_0027_step_0 : (774 : ℤ) = 1 * 510 + 264 := by
  norm_num

theorem v9long_test_0027_step_1 : (510 : ℤ) = 1 * 264 + 246 := by
  norm_num

theorem v9long_test_0027_step_2 : (264 : ℤ) = 1 * 246 + 18 := by
  norm_num

theorem v9long_test_0027_step_3 : (246 : ℤ) = 13 * 18 + 12 := by
  norm_num

theorem v9long_test_0027_step_4 : (18 : ℤ) = 1 * 12 + 6 := by
  norm_num

theorem v9long_test_0027_step_5 : (12 : ℤ) = 2 * 6 + 0 := by
  norm_num

theorem v9long_test_0027_divides : ¬ (6 : ℤ) ∣ (44 : ℤ) := by
  norm_num

theorem v9long_test_0027_conclusion : ¬ (∃ x y : ℤ, (44 : ℤ) = (510 : ℤ) * x + (774 : ℤ) * y) := by
  have hgcd : (Int.gcd (510 : ℤ) (774 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (510 : ℤ) (774 : ℤ) (44 : ℤ)).1 h
  rw [hgcd] at hd
  exact v9long_test_0027_divides hd

theorem v9long_test_0028_gcd : Nat.gcd 616 928 = 8 := by
  norm_num [Nat.gcd]

theorem v9long_test_0028_step_0 : (928 : ℤ) = 1 * 616 + 312 := by
  norm_num

theorem v9long_test_0028_step_1 : (616 : ℤ) = 1 * 312 + 304 := by
  norm_num

theorem v9long_test_0028_step_2 : (312 : ℤ) = 1 * 304 + 8 := by
  norm_num

theorem v9long_test_0028_step_3 : (304 : ℤ) = 38 * 8 + 0 := by
  norm_num

theorem v9long_test_0028_divides : (8 : ℤ) ∣ (168 : ℤ) := by
  norm_num

theorem v9long_test_0028_conclusion : ∃ x y : ℤ, (168 : ℤ) = (616 : ℤ) * x + (928 : ℤ) * y := by
  have hgcd : (Int.gcd (616 : ℤ) (928 : ℤ) : ℤ) = 8 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (616 : ℤ) (928 : ℤ) (168 : ℤ)).2
  simpa [hgcd] using v9long_test_0028_divides

theorem v9long_test_0032_gcd : Nat.gcd 225 610 = 5 := by
  norm_num [Nat.gcd]

theorem v9long_test_0032_step_0 : (610 : ℤ) = 2 * 225 + 160 := by
  norm_num

theorem v9long_test_0032_step_1 : (225 : ℤ) = 1 * 160 + 65 := by
  norm_num

theorem v9long_test_0032_step_2 : (160 : ℤ) = 2 * 65 + 30 := by
  norm_num

theorem v9long_test_0032_step_3 : (65 : ℤ) = 2 * 30 + 5 := by
  norm_num

theorem v9long_test_0032_step_4 : (30 : ℤ) = 6 * 5 + 0 := by
  norm_num

theorem v9long_test_0032_divides : (5 : ℤ) ∣ (-110 : ℤ) := by
  norm_num

theorem v9long_test_0032_conclusion : ∃ x y : ℤ, (-110 : ℤ) = (225 : ℤ) * x + (610 : ℤ) * y := by
  have hgcd : (Int.gcd (225 : ℤ) (610 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (225 : ℤ) (610 : ℤ) (-110 : ℤ)).2
  simpa [hgcd] using v9long_test_0032_divides

theorem v9long_test_0035_gcd : Nat.gcd 480 441 = 3 := by
  norm_num [Nat.gcd]

theorem v9long_test_0035_step_0 : (480 : ℤ) = 1 * 441 + 39 := by
  norm_num

theorem v9long_test_0035_step_1 : (441 : ℤ) = 11 * 39 + 12 := by
  norm_num

theorem v9long_test_0035_step_2 : (39 : ℤ) = 3 * 12 + 3 := by
  norm_num

theorem v9long_test_0035_step_3 : (12 : ℤ) = 4 * 3 + 0 := by
  norm_num

theorem v9long_test_0035_divides : ¬ (3 : ℤ) ∣ (-46 : ℤ) := by
  norm_num

theorem v9long_test_0035_conclusion : ¬ (∃ x y : ℤ, (-46 : ℤ) = (480 : ℤ) * x + (441 : ℤ) * y) := by
  have hgcd : (Int.gcd (480 : ℤ) (441 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (480 : ℤ) (441 : ℤ) (-46 : ℤ)).1 h
  rw [hgcd] at hd
  exact v9long_test_0035_divides hd

theorem v9long_test_0039_gcd : Nat.gcd 100 676 = 4 := by
  norm_num [Nat.gcd]

theorem v9long_test_0039_step_0 : (676 : ℤ) = 6 * 100 + 76 := by
  norm_num

theorem v9long_test_0039_step_1 : (100 : ℤ) = 1 * 76 + 24 := by
  norm_num

theorem v9long_test_0039_step_2 : (76 : ℤ) = 3 * 24 + 4 := by
  norm_num

theorem v9long_test_0039_step_3 : (24 : ℤ) = 6 * 4 + 0 := by
  norm_num

theorem v9long_test_0039_divides : ¬ (4 : ℤ) ∣ (11 : ℤ) := by
  norm_num

theorem v9long_test_0039_conclusion : ¬ (∃ x y : ℤ, (11 : ℤ) = (100 : ℤ) * x + (676 : ℤ) * y) := by
  have hgcd : (Int.gcd (100 : ℤ) (676 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (100 : ℤ) (676 : ℤ) (11 : ℤ)).1 h
  rw [hgcd] at hd
  exact v9long_test_0039_divides hd

theorem v9long_test_0040_gcd : Nat.gcd 556 772 = 4 := by
  norm_num [Nat.gcd]

theorem v9long_test_0040_step_0 : (772 : ℤ) = 1 * 556 + 216 := by
  norm_num

theorem v9long_test_0040_step_1 : (556 : ℤ) = 2 * 216 + 124 := by
  norm_num

theorem v9long_test_0040_step_2 : (216 : ℤ) = 1 * 124 + 92 := by
  norm_num

theorem v9long_test_0040_step_3 : (124 : ℤ) = 1 * 92 + 32 := by
  norm_num

theorem v9long_test_0040_step_4 : (92 : ℤ) = 2 * 32 + 28 := by
  norm_num

theorem v9long_test_0040_step_5 : (32 : ℤ) = 1 * 28 + 4 := by
  norm_num

theorem v9long_test_0040_step_6 : (28 : ℤ) = 7 * 4 + 0 := by
  norm_num

theorem v9long_test_0040_divides : (4 : ℤ) ∣ (-36 : ℤ) := by
  norm_num

theorem v9long_test_0040_conclusion : ∃ x y : ℤ, (-36 : ℤ) = (556 : ℤ) * x + (772 : ℤ) * y := by
  have hgcd : (Int.gcd (556 : ℤ) (772 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (556 : ℤ) (772 : ℤ) (-36 : ℤ)).2
  simpa [hgcd] using v9long_test_0040_divides

theorem v9long_test_0044_gcd : Nat.gcd 24 254 = 2 := by
  norm_num [Nat.gcd]

theorem v9long_test_0044_step_0 : (254 : ℤ) = 10 * 24 + 14 := by
  norm_num

theorem v9long_test_0044_step_1 : (24 : ℤ) = 1 * 14 + 10 := by
  norm_num

theorem v9long_test_0044_step_2 : (14 : ℤ) = 1 * 10 + 4 := by
  norm_num

theorem v9long_test_0044_step_3 : (10 : ℤ) = 2 * 4 + 2 := by
  norm_num

theorem v9long_test_0044_step_4 : (4 : ℤ) = 2 * 2 + 0 := by
  norm_num

theorem v9long_test_0044_divides : (2 : ℤ) ∣ (50 : ℤ) := by
  norm_num

theorem v9long_test_0044_conclusion : ∃ x y : ℤ, (50 : ℤ) = (24 : ℤ) * x + (254 : ℤ) * y := by
  have hgcd : (Int.gcd (24 : ℤ) (254 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (24 : ℤ) (254 : ℤ) (50 : ℤ)).2
  simpa [hgcd] using v9long_test_0044_divides

theorem v9long_test_0045_gcd : Nat.gcd 808 952 = 8 := by
  norm_num [Nat.gcd]

theorem v9long_test_0045_step_0 : (952 : ℤ) = 1 * 808 + 144 := by
  norm_num

theorem v9long_test_0045_step_1 : (808 : ℤ) = 5 * 144 + 88 := by
  norm_num

theorem v9long_test_0045_step_2 : (144 : ℤ) = 1 * 88 + 56 := by
  norm_num

theorem v9long_test_0045_step_3 : (88 : ℤ) = 1 * 56 + 32 := by
  norm_num

theorem v9long_test_0045_step_4 : (56 : ℤ) = 1 * 32 + 24 := by
  norm_num

theorem v9long_test_0045_step_5 : (32 : ℤ) = 1 * 24 + 8 := by
  norm_num

theorem v9long_test_0045_step_6 : (24 : ℤ) = 3 * 8 + 0 := by
  norm_num

theorem v9long_test_0045_divides : ¬ (8 : ℤ) ∣ (-187 : ℤ) := by
  norm_num

theorem v9long_test_0045_conclusion : ¬ (∃ x y : ℤ, (-187 : ℤ) = (808 : ℤ) * x + (952 : ℤ) * y) := by
  have hgcd : (Int.gcd (808 : ℤ) (952 : ℤ) : ℤ) = 8 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (808 : ℤ) (952 : ℤ) (-187 : ℤ)).1 h
  rw [hgcd] at hd
  exact v9long_test_0045_divides hd

theorem v9long_test_0048_gcd : Nat.gcd 524 404 = 4 := by
  norm_num [Nat.gcd]

theorem v9long_test_0048_step_0 : (524 : ℤ) = 1 * 404 + 120 := by
  norm_num

theorem v9long_test_0048_step_1 : (404 : ℤ) = 3 * 120 + 44 := by
  norm_num

theorem v9long_test_0048_step_2 : (120 : ℤ) = 2 * 44 + 32 := by
  norm_num

theorem v9long_test_0048_step_3 : (44 : ℤ) = 1 * 32 + 12 := by
  norm_num

theorem v9long_test_0048_step_4 : (32 : ℤ) = 2 * 12 + 8 := by
  norm_num

theorem v9long_test_0048_step_5 : (12 : ℤ) = 1 * 8 + 4 := by
  norm_num

theorem v9long_test_0048_step_6 : (8 : ℤ) = 2 * 4 + 0 := by
  norm_num

theorem v9long_test_0048_divides : (4 : ℤ) ∣ (40 : ℤ) := by
  norm_num

theorem v9long_test_0048_conclusion : ∃ x y : ℤ, (40 : ℤ) = (524 : ℤ) * x + (404 : ℤ) * y := by
  have hgcd : (Int.gcd (524 : ℤ) (404 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (524 : ℤ) (404 : ℤ) (40 : ℤ)).2
  simpa [hgcd] using v9long_test_0048_divides

theorem v9short_test_0001_gcd : Nat.gcd 50 98 = 2 := by
  norm_num [Nat.gcd]

theorem v9short_test_0001_step_0 : (98 : ℤ) = 1 * 50 + 48 := by
  norm_num

theorem v9short_test_0001_step_1 : (50 : ℤ) = 1 * 48 + 2 := by
  norm_num

theorem v9short_test_0001_step_2 : (48 : ℤ) = 24 * 2 + 0 := by
  norm_num

theorem v9short_test_0001_divides : ¬ (2 : ℤ) ∣ (37 : ℤ) := by
  norm_num

theorem v9short_test_0001_conclusion : ¬ (∃ x y : ℤ, (37 : ℤ) = (50 : ℤ) * x + (98 : ℤ) * y) := by
  have hgcd : (Int.gcd (50 : ℤ) (98 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (50 : ℤ) (98 : ℤ) (37 : ℤ)).1 h
  rw [hgcd] at hd
  exact v9short_test_0001_divides hd

theorem v9short_test_0004_gcd : Nat.gcd 565 80 = 5 := by
  norm_num [Nat.gcd]

theorem v9short_test_0004_step_0 : (565 : ℤ) = 7 * 80 + 5 := by
  norm_num

theorem v9short_test_0004_step_1 : (80 : ℤ) = 16 * 5 + 0 := by
  norm_num

theorem v9short_test_0004_divides : (5 : ℤ) ∣ (100 : ℤ) := by
  norm_num

theorem v9short_test_0004_conclusion : ∃ x y : ℤ, (100 : ℤ) = (565 : ℤ) * x + (80 : ℤ) * y := by
  have hgcd : (Int.gcd (565 : ℤ) (80 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (565 : ℤ) (80 : ℤ) (100 : ℤ)).2
  simpa [hgcd] using v9short_test_0004_divides

theorem v9short_test_0008_gcd : Nat.gcd 385 364 = 7 := by
  norm_num [Nat.gcd]

theorem v9short_test_0008_step_0 : (385 : ℤ) = 1 * 364 + 21 := by
  norm_num

theorem v9short_test_0008_step_1 : (364 : ℤ) = 17 * 21 + 7 := by
  norm_num

theorem v9short_test_0008_step_2 : (21 : ℤ) = 3 * 7 + 0 := by
  norm_num

theorem v9short_test_0008_divides : (7 : ℤ) ∣ (-21 : ℤ) := by
  norm_num

theorem v9short_test_0008_conclusion : ∃ x y : ℤ, (-21 : ℤ) = (385 : ℤ) * x + (364 : ℤ) * y := by
  have hgcd : (Int.gcd (385 : ℤ) (364 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (385 : ℤ) (364 : ℤ) (-21 : ℤ)).2
  simpa [hgcd] using v9short_test_0008_divides

theorem v9short_test_0010_gcd : Nat.gcd 468 464 = 4 := by
  norm_num [Nat.gcd]

theorem v9short_test_0010_step_0 : (468 : ℤ) = 1 * 464 + 4 := by
  norm_num

theorem v9short_test_0010_step_1 : (464 : ℤ) = 116 * 4 + 0 := by
  norm_num

theorem v9short_test_0010_divides : (4 : ℤ) ∣ (-36 : ℤ) := by
  norm_num

theorem v9short_test_0010_conclusion : ∃ x y : ℤ, (-36 : ℤ) = (468 : ℤ) * x + (464 : ℤ) * y := by
  have hgcd : (Int.gcd (468 : ℤ) (464 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (468 : ℤ) (464 : ℤ) (-36 : ℤ)).2
  simpa [hgcd] using v9short_test_0010_divides

theorem v9short_test_0012_gcd : Nat.gcd 255 273 = 3 := by
  norm_num [Nat.gcd]

theorem v9short_test_0012_step_0 : (273 : ℤ) = 1 * 255 + 18 := by
  norm_num

theorem v9short_test_0012_step_1 : (255 : ℤ) = 14 * 18 + 3 := by
  norm_num

theorem v9short_test_0012_step_2 : (18 : ℤ) = 6 * 3 + 0 := by
  norm_num

theorem v9short_test_0012_divides : (3 : ℤ) ∣ (-33 : ℤ) := by
  norm_num

theorem v9short_test_0012_conclusion : ∃ x y : ℤ, (-33 : ℤ) = (255 : ℤ) * x + (273 : ℤ) * y := by
  have hgcd : (Int.gcd (255 : ℤ) (273 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (255 : ℤ) (273 : ℤ) (-33 : ℤ)).2
  simpa [hgcd] using v9short_test_0012_divides

theorem v9short_test_0016_gcd : Nat.gcd 480 489 = 3 := by
  norm_num [Nat.gcd]

theorem v9short_test_0016_step_0 : (489 : ℤ) = 1 * 480 + 9 := by
  norm_num

theorem v9short_test_0016_step_1 : (480 : ℤ) = 53 * 9 + 3 := by
  norm_num

theorem v9short_test_0016_step_2 : (9 : ℤ) = 3 * 3 + 0 := by
  norm_num

theorem v9short_test_0016_divides : (3 : ℤ) ∣ (-48 : ℤ) := by
  norm_num

theorem v9short_test_0016_conclusion : ∃ x y : ℤ, (-48 : ℤ) = (480 : ℤ) * x + (489 : ℤ) * y := by
  have hgcd : (Int.gcd (480 : ℤ) (489 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (480 : ℤ) (489 : ℤ) (-48 : ℤ)).2
  simpa [hgcd] using v9short_test_0016_divides

theorem v9short_test_0017_gcd : Nat.gcd 32 6 = 2 := by
  norm_num [Nat.gcd]

theorem v9short_test_0017_step_0 : (32 : ℤ) = 5 * 6 + 2 := by
  norm_num

theorem v9short_test_0017_step_1 : (6 : ℤ) = 3 * 2 + 0 := by
  norm_num

theorem v9short_test_0017_divides : ¬ (2 : ℤ) ∣ (13 : ℤ) := by
  norm_num

theorem v9short_test_0017_conclusion : ¬ (∃ x y : ℤ, (13 : ℤ) = (32 : ℤ) * x + (6 : ℤ) * y) := by
  have hgcd : (Int.gcd (32 : ℤ) (6 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (32 : ℤ) (6 : ℤ) (13 : ℤ)).1 h
  rw [hgcd] at hd
  exact v9short_test_0017_divides hd

theorem v9short_test_0018_gcd : Nat.gcd 781 803 = 11 := by
  norm_num [Nat.gcd]

theorem v9short_test_0018_step_0 : (803 : ℤ) = 1 * 781 + 22 := by
  norm_num

theorem v9short_test_0018_step_1 : (781 : ℤ) = 35 * 22 + 11 := by
  norm_num

theorem v9short_test_0018_step_2 : (22 : ℤ) = 2 * 11 + 0 := by
  norm_num

theorem v9short_test_0018_divides : (11 : ℤ) ∣ (-121 : ℤ) := by
  norm_num

theorem v9short_test_0018_conclusion : ∃ x y : ℤ, (-121 : ℤ) = (781 : ℤ) * x + (803 : ℤ) * y := by
  have hgcd : (Int.gcd (781 : ℤ) (803 : ℤ) : ℤ) = 11 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (781 : ℤ) (803 : ℤ) (-121 : ℤ)).2
  simpa [hgcd] using v9short_test_0018_divides

theorem v9short_test_0019_gcd : Nat.gcd 336 63 = 21 := by
  norm_num [Nat.gcd]

theorem v9short_test_0019_step_0 : (336 : ℤ) = 5 * 63 + 21 := by
  norm_num

theorem v9short_test_0019_step_1 : (63 : ℤ) = 3 * 21 + 0 := by
  norm_num

theorem v9short_test_0019_divides : ¬ (21 : ℤ) ∣ (502 : ℤ) := by
  norm_num

theorem v9short_test_0019_conclusion : ¬ (∃ x y : ℤ, (502 : ℤ) = (336 : ℤ) * x + (63 : ℤ) * y) := by
  have hgcd : (Int.gcd (336 : ℤ) (63 : ℤ) : ℤ) = 21 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (336 : ℤ) (63 : ℤ) (502 : ℤ)).1 h
  rw [hgcd] at hd
  exact v9short_test_0019_divides hd

theorem v9short_test_0036_gcd : Nat.gcd 308 286 = 22 := by
  norm_num [Nat.gcd]

theorem v9short_test_0036_step_0 : (308 : ℤ) = 1 * 286 + 22 := by
  norm_num

theorem v9short_test_0036_step_1 : (286 : ℤ) = 13 * 22 + 0 := by
  norm_num

theorem v9short_test_0036_divides : (22 : ℤ) ∣ (-88 : ℤ) := by
  norm_num

theorem v9short_test_0036_conclusion : ∃ x y : ℤ, (-88 : ℤ) = (308 : ℤ) * x + (286 : ℤ) * y := by
  have hgcd : (Int.gcd (308 : ℤ) (286 : ℤ) : ℤ) = 22 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (308 : ℤ) (286 : ℤ) (-88 : ℤ)).2
  simpa [hgcd] using v9short_test_0036_divides

theorem v9short_test_0040_gcd : Nat.gcd 447 435 = 3 := by
  norm_num [Nat.gcd]

theorem v9short_test_0040_step_0 : (447 : ℤ) = 1 * 435 + 12 := by
  norm_num

theorem v9short_test_0040_step_1 : (435 : ℤ) = 36 * 12 + 3 := by
  norm_num

theorem v9short_test_0040_step_2 : (12 : ℤ) = 4 * 3 + 0 := by
  norm_num

theorem v9short_test_0040_divides : (3 : ℤ) ∣ (21 : ℤ) := by
  norm_num

theorem v9short_test_0040_conclusion : ∃ x y : ℤ, (21 : ℤ) = (447 : ℤ) * x + (435 : ℤ) * y := by
  have hgcd : (Int.gcd (447 : ℤ) (435 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (447 : ℤ) (435 : ℤ) (21 : ℤ)).2
  simpa [hgcd] using v9short_test_0040_divides

theorem v9short_test_0049_gcd : Nat.gcd 120 460 = 20 := by
  norm_num [Nat.gcd]

theorem v9short_test_0049_step_0 : (460 : ℤ) = 3 * 120 + 100 := by
  norm_num

theorem v9short_test_0049_step_1 : (120 : ℤ) = 1 * 100 + 20 := by
  norm_num

theorem v9short_test_0049_step_2 : (100 : ℤ) = 5 * 20 + 0 := by
  norm_num

theorem v9short_test_0049_divides : ¬ (20 : ℤ) ∣ (93 : ℤ) := by
  norm_num

theorem v9short_test_0049_conclusion : ¬ (∃ x y : ℤ, (93 : ℤ) = (120 : ℤ) * x + (460 : ℤ) * y) := by
  have hgcd : (Int.gcd (120 : ℤ) (460 : ℤ) : ℤ) = 20 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (120 : ℤ) (460 : ℤ) (93 : ℤ)).1 h
  rw [hgcd] at hd
  exact v9short_test_0049_divides hd

end AtomicClaimCertificates
