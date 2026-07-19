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

theorem dav2_test_0002_gcd : Nat.gcd 1717 2652 = 17 := by
  norm_num [Nat.gcd]

theorem dav2_test_0002_divides : (17 : ℤ) ∣ (-238 : ℤ) := by
  norm_num

theorem dav2_test_0002_conclusion : ∃ x y : ℤ, (-238 : ℤ) = (1717 : ℤ) * x + (2652 : ℤ) * y := by
  have hgcd : (Int.gcd (1717 : ℤ) (2652 : ℤ) : ℤ) = 17 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (1717 : ℤ) (2652 : ℤ) (-238 : ℤ)).2
  rw [hgcd]
  exact dav2_test_0002_divides

theorem dav2_test_0003_gcd : Nat.gcd 1875 3175 = 25 := by
  norm_num [Nat.gcd]

theorem dav2_test_0003_divides : ¬ (25 : ℤ) ∣ (-483 : ℤ) := by
  norm_num

theorem dav2_test_0003_conclusion : ¬ (∃ x y : ℤ, (-483 : ℤ) = (1875 : ℤ) * x + (3175 : ℤ) * y) := by
  have hgcd : (Int.gcd (1875 : ℤ) (3175 : ℤ) : ℤ) = 25 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (1875 : ℤ) (3175 : ℤ) (-483 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav2_test_0003_divides hd

theorem dav2_test_0007_gcd : Nat.gcd 715 345 = 5 := by
  norm_num [Nat.gcd]

theorem dav2_test_0007_divides : ¬ (5 : ℤ) ∣ (18 : ℤ) := by
  norm_num

theorem dav2_test_0007_conclusion : ¬ (∃ x y : ℤ, (18 : ℤ) = (715 : ℤ) * x + (345 : ℤ) * y) := by
  have hgcd : (Int.gcd (715 : ℤ) (345 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (715 : ℤ) (345 : ℤ) (18 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav2_test_0007_divides hd

theorem dav2_test_0014_gcd : Nat.gcd 468 568 = 4 := by
  norm_num [Nat.gcd]

theorem dav2_test_0014_divides : (4 : ℤ) ∣ (28 : ℤ) := by
  norm_num

theorem dav2_test_0014_conclusion : ∃ x y : ℤ, (28 : ℤ) = (468 : ℤ) * x + (568 : ℤ) * y := by
  have hgcd : (Int.gcd (468 : ℤ) (568 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (468 : ℤ) (568 : ℤ) (28 : ℤ)).2
  rw [hgcd]
  exact dav2_test_0014_divides

theorem dav2_test_0019_gcd : Nat.gcd 3390 1140 = 30 := by
  norm_num [Nat.gcd]

theorem dav2_test_0019_divides : ¬ (30 : ℤ) ∣ (-393 : ℤ) := by
  norm_num

theorem dav2_test_0019_conclusion : ¬ (∃ x y : ℤ, (-393 : ℤ) = (3390 : ℤ) * x + (1140 : ℤ) * y) := by
  have hgcd : (Int.gcd (3390 : ℤ) (1140 : ℤ) : ℤ) = 30 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (3390 : ℤ) (1140 : ℤ) (-393 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav2_test_0019_divides hd

theorem dav2_test_0023_gcd : Nat.gcd 684 192 = 12 := by
  norm_num [Nat.gcd]

theorem dav2_test_0023_divides : ¬ (12 : ℤ) ∣ (112 : ℤ) := by
  norm_num

theorem dav2_test_0023_conclusion : ¬ (∃ x y : ℤ, (112 : ℤ) = (684 : ℤ) * x + (192 : ℤ) * y) := by
  have hgcd : (Int.gcd (684 : ℤ) (192 : ℤ) : ℤ) = 12 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (684 : ℤ) (192 : ℤ) (112 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav2_test_0023_divides hd

theorem dav2_test_0027_gcd : Nat.gcd 960 1095 = 15 := by
  norm_num [Nat.gcd]

theorem dav2_test_0027_divides : ¬ (15 : ℤ) ∣ (-88 : ℤ) := by
  norm_num

theorem dav2_test_0027_conclusion : ¬ (∃ x y : ℤ, (-88 : ℤ) = (960 : ℤ) * x + (1095 : ℤ) * y) := by
  have hgcd : (Int.gcd (960 : ℤ) (1095 : ℤ) : ℤ) = 15 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (960 : ℤ) (1095 : ℤ) (-88 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav2_test_0027_divides hd

theorem dav2_test_0034_gcd : Nat.gcd 1670 20 = 10 := by
  norm_num [Nat.gcd]

theorem dav2_test_0034_divides : (10 : ℤ) ∣ (110 : ℤ) := by
  norm_num

theorem dav2_test_0034_conclusion : ∃ x y : ℤ, (110 : ℤ) = (1670 : ℤ) * x + (20 : ℤ) * y := by
  have hgcd : (Int.gcd (1670 : ℤ) (20 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (1670 : ℤ) (20 : ℤ) (110 : ℤ)).2
  rw [hgcd]
  exact dav2_test_0034_divides

theorem dav2_test_0035_gcd : Nat.gcd 2889 2592 = 27 := by
  norm_num [Nat.gcd]

theorem dav2_test_0035_divides : ¬ (27 : ℤ) ∣ (496 : ℤ) := by
  norm_num

theorem dav2_test_0035_conclusion : ¬ (∃ x y : ℤ, (496 : ℤ) = (2889 : ℤ) * x + (2592 : ℤ) * y) := by
  have hgcd : (Int.gcd (2889 : ℤ) (2592 : ℤ) : ℤ) = 27 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (2889 : ℤ) (2592 : ℤ) (496 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav2_test_0035_divides hd

theorem dav2_test_0037_gcd : Nat.gcd 3330 1740 = 30 := by
  norm_num [Nat.gcd]

theorem dav2_test_0037_divides : ¬ (30 : ℤ) ∣ (405 : ℤ) := by
  norm_num

theorem dav2_test_0037_conclusion : ¬ (∃ x y : ℤ, (405 : ℤ) = (3330 : ℤ) * x + (1740 : ℤ) * y) := by
  have hgcd : (Int.gcd (3330 : ℤ) (1740 : ℤ) : ℤ) = 30 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (3330 : ℤ) (1740 : ℤ) (405 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav2_test_0037_divides hd

theorem dav2_test_0038_gcd : Nat.gcd 1152 2568 = 24 := by
  norm_num [Nat.gcd]

theorem dav2_test_0038_divides : (24 : ℤ) ∣ (264 : ℤ) := by
  norm_num

theorem dav2_test_0038_conclusion : ∃ x y : ℤ, (264 : ℤ) = (1152 : ℤ) * x + (2568 : ℤ) * y := by
  have hgcd : (Int.gcd (1152 : ℤ) (2568 : ℤ) : ℤ) = 24 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (1152 : ℤ) (2568 : ℤ) (264 : ℤ)).2
  rw [hgcd]
  exact dav2_test_0038_divides

theorem dav2_test_0048_gcd : Nat.gcd 132 583 = 11 := by
  norm_num [Nat.gcd]

theorem dav2_test_0048_divides : (11 : ℤ) ∣ (220 : ℤ) := by
  norm_num

theorem dav2_test_0048_conclusion : ∃ x y : ℤ, (220 : ℤ) = (132 : ℤ) * x + (583 : ℤ) * y := by
  have hgcd : (Int.gcd (132 : ℤ) (583 : ℤ) : ℤ) = 11 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (132 : ℤ) (583 : ℤ) (220 : ℤ)).2
  rw [hgcd]
  exact dav2_test_0048_divides

theorem dav2_test_0049_gcd : Nat.gcd 550 430 = 10 := by
  norm_num [Nat.gcd]

theorem dav2_test_0049_divides : ¬ (10 : ℤ) ∣ (38 : ℤ) := by
  norm_num

theorem dav2_test_0049_conclusion : ¬ (∃ x y : ℤ, (38 : ℤ) = (550 : ℤ) * x + (430 : ℤ) * y) := by
  have hgcd : (Int.gcd (550 : ℤ) (430 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (550 : ℤ) (430 : ℤ) (38 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav2_test_0049_divides hd

theorem dav2_test_0052_gcd : Nat.gcd 2505 1365 = 15 := by
  norm_num [Nat.gcd]

theorem dav2_test_0052_divides : (15 : ℤ) ∣ (-240 : ℤ) := by
  norm_num

theorem dav2_test_0052_conclusion : ∃ x y : ℤ, (-240 : ℤ) = (2505 : ℤ) * x + (1365 : ℤ) * y := by
  have hgcd : (Int.gcd (2505 : ℤ) (1365 : ℤ) : ℤ) = 15 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (2505 : ℤ) (1365 : ℤ) (-240 : ℤ)).2
  rw [hgcd]
  exact dav2_test_0052_divides

theorem dav2_test_0054_gcd : Nat.gcd 96 1048 = 8 := by
  norm_num [Nat.gcd]

theorem dav2_test_0054_divides : (8 : ℤ) ∣ (72 : ℤ) := by
  norm_num

theorem dav2_test_0054_conclusion : ∃ x y : ℤ, (72 : ℤ) = (96 : ℤ) * x + (1048 : ℤ) * y := by
  have hgcd : (Int.gcd (96 : ℤ) (1048 : ℤ) : ℤ) = 8 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (96 : ℤ) (1048 : ℤ) (72 : ℤ)).2
  rw [hgcd]
  exact dav2_test_0054_divides

theorem dav2_test_0055_gcd : Nat.gcd 366 294 = 6 := by
  norm_num [Nat.gcd]

theorem dav2_test_0055_divides : ¬ (6 : ℤ) ∣ (35 : ℤ) := by
  norm_num

theorem dav2_test_0055_conclusion : ¬ (∃ x y : ℤ, (35 : ℤ) = (366 : ℤ) * x + (294 : ℤ) * y) := by
  have hgcd : (Int.gcd (366 : ℤ) (294 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (366 : ℤ) (294 : ℤ) (35 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav2_test_0055_divides hd

theorem dav2_test_0058_gcd : Nat.gcd 612 2790 = 18 := by
  norm_num [Nat.gcd]

theorem dav2_test_0058_divides : (18 : ℤ) ∣ (360 : ℤ) := by
  norm_num

theorem dav2_test_0058_conclusion : ∃ x y : ℤ, (360 : ℤ) = (612 : ℤ) * x + (2790 : ℤ) * y := by
  have hgcd : (Int.gcd (612 : ℤ) (2790 : ℤ) : ℤ) = 18 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (612 : ℤ) (2790 : ℤ) (360 : ℤ)).2
  rw [hgcd]
  exact dav2_test_0058_divides

theorem dav2_test_0060_gcd : Nat.gcd 1005 2355 = 15 := by
  norm_num [Nat.gcd]

theorem dav2_test_0060_divides : (15 : ℤ) ∣ (135 : ℤ) := by
  norm_num

theorem dav2_test_0060_conclusion : ∃ x y : ℤ, (135 : ℤ) = (1005 : ℤ) * x + (2355 : ℤ) * y := by
  have hgcd : (Int.gcd (1005 : ℤ) (2355 : ℤ) : ℤ) = 15 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (1005 : ℤ) (2355 : ℤ) (135 : ℤ)).2
  rw [hgcd]
  exact dav2_test_0060_divides

theorem dav2_test_0062_gcd : Nat.gcd 1584 496 = 16 := by
  norm_num [Nat.gcd]

theorem dav2_test_0062_divides : (16 : ℤ) ∣ (16 : ℤ) := by
  norm_num

theorem dav2_test_0062_conclusion : ∃ x y : ℤ, (16 : ℤ) = (1584 : ℤ) * x + (496 : ℤ) * y := by
  have hgcd : (Int.gcd (1584 : ℤ) (496 : ℤ) : ℤ) = 16 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (1584 : ℤ) (496 : ℤ) (16 : ℤ)).2
  rw [hgcd]
  exact dav2_test_0062_divides

theorem dav2_test_0064_gcd : Nat.gcd 1206 1638 = 18 := by
  norm_num [Nat.gcd]

theorem dav2_test_0064_divides : (18 : ℤ) ∣ (-36 : ℤ) := by
  norm_num

theorem dav2_test_0064_conclusion : ∃ x y : ℤ, (-36 : ℤ) = (1206 : ℤ) * x + (1638 : ℤ) * y := by
  have hgcd : (Int.gcd (1206 : ℤ) (1638 : ℤ) : ℤ) = 18 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (1206 : ℤ) (1638 : ℤ) (-36 : ℤ)).2
  rw [hgcd]
  exact dav2_test_0064_divides

theorem dav2_test_0069_gcd : Nat.gcd 102 345 = 3 := by
  norm_num [Nat.gcd]

theorem dav2_test_0069_divides : ¬ (3 : ℤ) ∣ (62 : ℤ) := by
  norm_num

theorem dav2_test_0069_conclusion : ¬ (∃ x y : ℤ, (62 : ℤ) = (102 : ℤ) * x + (345 : ℤ) * y) := by
  have hgcd : (Int.gcd (102 : ℤ) (345 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (102 : ℤ) (345 : ℤ) (62 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav2_test_0069_divides hd

theorem dav2_test_0075_gcd : Nat.gcd 986 1411 = 17 := by
  norm_num [Nat.gcd]

theorem dav2_test_0075_divides : ¬ (17 : ℤ) ∣ (283 : ℤ) := by
  norm_num

theorem dav2_test_0075_conclusion : ¬ (∃ x y : ℤ, (283 : ℤ) = (986 : ℤ) * x + (1411 : ℤ) * y) := by
  have hgcd : (Int.gcd (986 : ℤ) (1411 : ℤ) : ℤ) = 17 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (986 : ℤ) (1411 : ℤ) (283 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav2_test_0075_divides hd

theorem dav2_test_0077_gcd : Nat.gcd 959 1008 = 7 := by
  norm_num [Nat.gcd]

theorem dav2_test_0077_divides : ¬ (7 : ℤ) ∣ (-116 : ℤ) := by
  norm_num

theorem dav2_test_0077_conclusion : ¬ (∃ x y : ℤ, (-116 : ℤ) = (959 : ℤ) * x + (1008 : ℤ) * y) := by
  have hgcd : (Int.gcd (959 : ℤ) (1008 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (959 : ℤ) (1008 : ℤ) (-116 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav2_test_0077_divides hd

theorem dav2_test_0081_gcd : Nat.gcd 210 2280 = 30 := by
  norm_num [Nat.gcd]

theorem dav2_test_0081_divides : ¬ (30 : ℤ) ∣ (-222 : ℤ) := by
  norm_num

theorem dav2_test_0081_conclusion : ¬ (∃ x y : ℤ, (-222 : ℤ) = (210 : ℤ) * x + (2280 : ℤ) * y) := by
  have hgcd : (Int.gcd (210 : ℤ) (2280 : ℤ) : ℤ) = 30 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (210 : ℤ) (2280 : ℤ) (-222 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav2_test_0081_divides hd

theorem dav2_test_0094_gcd : Nat.gcd 2940 460 = 20 := by
  norm_num [Nat.gcd]

theorem dav2_test_0094_divides : (20 : ℤ) ∣ (-220 : ℤ) := by
  norm_num

theorem dav2_test_0094_conclusion : ∃ x y : ℤ, (-220 : ℤ) = (2940 : ℤ) * x + (460 : ℤ) * y := by
  have hgcd : (Int.gcd (2940 : ℤ) (460 : ℤ) : ℤ) = 20 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (2940 : ℤ) (460 : ℤ) (-220 : ℤ)).2
  rw [hgcd]
  exact dav2_test_0094_divides

theorem dav2_test_0096_gcd : Nat.gcd 3175 875 = 25 := by
  norm_num [Nat.gcd]

theorem dav2_test_0096_divides : (25 : ℤ) ∣ (475 : ℤ) := by
  norm_num

theorem dav2_test_0096_conclusion : ∃ x y : ℤ, (475 : ℤ) = (3175 : ℤ) * x + (875 : ℤ) * y := by
  have hgcd : (Int.gcd (3175 : ℤ) (875 : ℤ) : ℤ) = 25 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (3175 : ℤ) (875 : ℤ) (475 : ℤ)).2
  rw [hgcd]
  exact dav2_test_0096_divides

theorem dav2_test_0103_gcd : Nat.gcd 2384 2688 = 16 := by
  norm_num [Nat.gcd]

theorem dav2_test_0103_divides : ¬ (16 : ℤ) ∣ (-271 : ℤ) := by
  norm_num

theorem dav2_test_0103_conclusion : ¬ (∃ x y : ℤ, (-271 : ℤ) = (2384 : ℤ) * x + (2688 : ℤ) * y) := by
  have hgcd : (Int.gcd (2384 : ℤ) (2688 : ℤ) : ℤ) = 16 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (2384 : ℤ) (2688 : ℤ) (-271 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav2_test_0103_divides hd

theorem dav2_test_0121_gcd : Nat.gcd 452 352 = 4 := by
  norm_num [Nat.gcd]

theorem dav2_test_0121_divides : ¬ (4 : ℤ) ∣ (65 : ℤ) := by
  norm_num

theorem dav2_test_0121_conclusion : ¬ (∃ x y : ℤ, (65 : ℤ) = (452 : ℤ) * x + (352 : ℤ) * y) := by
  have hgcd : (Int.gcd (452 : ℤ) (352 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (452 : ℤ) (352 : ℤ) (65 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav2_test_0121_divides hd

theorem dav2_test_0137_gcd : Nat.gcd 819 45 = 9 := by
  norm_num [Nat.gcd]

theorem dav2_test_0137_divides : ¬ (9 : ℤ) ∣ (152 : ℤ) := by
  norm_num

theorem dav2_test_0137_conclusion : ¬ (∃ x y : ℤ, (152 : ℤ) = (819 : ℤ) * x + (45 : ℤ) * y) := by
  have hgcd : (Int.gcd (819 : ℤ) (45 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (819 : ℤ) (45 : ℤ) (152 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav2_test_0137_divides hd

theorem dav2_test_0155_gcd : Nat.gcd 1935 1995 = 15 := by
  norm_num [Nat.gcd]

theorem dav2_test_0155_divides : ¬ (15 : ℤ) ∣ (32 : ℤ) := by
  norm_num

theorem dav2_test_0155_conclusion : ¬ (∃ x y : ℤ, (32 : ℤ) = (1935 : ℤ) * x + (1995 : ℤ) * y) := by
  have hgcd : (Int.gcd (1935 : ℤ) (1995 : ℤ) : ℤ) = 15 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (1935 : ℤ) (1995 : ℤ) (32 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav2_test_0155_divides hd

theorem dav2_test_0167_gcd : Nat.gcd 1440 1328 = 16 := by
  norm_num [Nat.gcd]

theorem dav2_test_0167_divides : ¬ (16 : ℤ) ∣ (248 : ℤ) := by
  norm_num

theorem dav2_test_0167_conclusion : ¬ (∃ x y : ℤ, (248 : ℤ) = (1440 : ℤ) * x + (1328 : ℤ) * y) := by
  have hgcd : (Int.gcd (1440 : ℤ) (1328 : ℤ) : ℤ) = 16 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (1440 : ℤ) (1328 : ℤ) (248 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav2_test_0167_divides hd

theorem dav2_test_0179_gcd : Nat.gcd 2160 1062 = 18 := by
  norm_num [Nat.gcd]

theorem dav2_test_0179_divides : ¬ (18 : ℤ) ∣ (231 : ℤ) := by
  norm_num

theorem dav2_test_0179_conclusion : ¬ (∃ x y : ℤ, (231 : ℤ) = (2160 : ℤ) * x + (1062 : ℤ) * y) := by
  have hgcd : (Int.gcd (2160 : ℤ) (1062 : ℤ) : ℤ) = 18 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (2160 : ℤ) (1062 : ℤ) (231 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav2_test_0179_divides hd

end AtomicClaimCertificates
