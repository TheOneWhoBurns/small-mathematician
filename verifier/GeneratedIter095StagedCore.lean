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

theorem v18_large_long_test_0005_gcd : Nat.gcd 1557 180 = 9 := by
  norm_num [Nat.gcd]

theorem v18_large_long_test_0005_step_0 : (1557 : ℤ) = 8 * 180 + 117 := by
  norm_num

theorem v18_large_long_test_0005_step_1 : (180 : ℤ) = 1 * 117 + 63 := by
  norm_num

theorem v18_large_long_test_0005_step_2 : (117 : ℤ) = 1 * 63 + 54 := by
  norm_num

theorem v18_large_long_test_0005_step_3 : (63 : ℤ) = 1 * 54 + 9 := by
  norm_num

theorem v18_large_long_test_0005_step_4 : (54 : ℤ) = 6 * 9 + 0 := by
  norm_num

theorem v18_large_long_test_0005_divides : ¬ (9 : ℤ) ∣ (88 : ℤ) := by
  norm_num

theorem v18_large_long_test_0005_conclusion : ¬ (∃ x y : ℤ, (88 : ℤ) = (1557 : ℤ) * x + (180 : ℤ) * y) := by
  have hgcd : (Int.gcd (1557 : ℤ) (180 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (1557 : ℤ) (180 : ℤ) (88 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_large_long_test_0005_divides hd

theorem v18_large_long_test_0013_gcd : Nat.gcd 1232 1980 = 44 := by
  norm_num [Nat.gcd]

theorem v18_large_long_test_0013_step_0 : (1980 : ℤ) = 1 * 1232 + 748 := by
  norm_num

theorem v18_large_long_test_0013_step_1 : (1232 : ℤ) = 1 * 748 + 484 := by
  norm_num

theorem v18_large_long_test_0013_step_2 : (748 : ℤ) = 1 * 484 + 264 := by
  norm_num

theorem v18_large_long_test_0013_step_3 : (484 : ℤ) = 1 * 264 + 220 := by
  norm_num

theorem v18_large_long_test_0013_step_4 : (264 : ℤ) = 1 * 220 + 44 := by
  norm_num

theorem v18_large_long_test_0013_step_5 : (220 : ℤ) = 5 * 44 + 0 := by
  norm_num

theorem v18_large_long_test_0013_divides : ¬ (44 : ℤ) ∣ (-678 : ℤ) := by
  norm_num

theorem v18_large_long_test_0013_conclusion : ¬ (∃ x y : ℤ, (-678 : ℤ) = (1232 : ℤ) * x + (1980 : ℤ) * y) := by
  have hgcd : (Int.gcd (1232 : ℤ) (1980 : ℤ) : ℤ) = 44 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (1232 : ℤ) (1980 : ℤ) (-678 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_large_long_test_0013_divides hd

theorem v18_large_long_test_0015_gcd : Nat.gcd 1158 420 = 6 := by
  norm_num [Nat.gcd]

theorem v18_large_long_test_0015_step_0 : (1158 : ℤ) = 2 * 420 + 318 := by
  norm_num

theorem v18_large_long_test_0015_step_1 : (420 : ℤ) = 1 * 318 + 102 := by
  norm_num

theorem v18_large_long_test_0015_step_2 : (318 : ℤ) = 3 * 102 + 12 := by
  norm_num

theorem v18_large_long_test_0015_step_3 : (102 : ℤ) = 8 * 12 + 6 := by
  norm_num

theorem v18_large_long_test_0015_step_4 : (12 : ℤ) = 2 * 6 + 0 := by
  norm_num

theorem v18_large_long_test_0015_divides : ¬ (6 : ℤ) ∣ (23 : ℤ) := by
  norm_num

theorem v18_large_long_test_0015_conclusion : ¬ (∃ x y : ℤ, (23 : ℤ) = (1158 : ℤ) * x + (420 : ℤ) * y) := by
  have hgcd : (Int.gcd (1158 : ℤ) (420 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (1158 : ℤ) (420 : ℤ) (23 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_large_long_test_0015_divides hd

theorem v18_large_long_test_0019_gcd : Nat.gcd 1830 2490 = 30 := by
  norm_num [Nat.gcd]

theorem v18_large_long_test_0019_step_0 : (2490 : ℤ) = 1 * 1830 + 660 := by
  norm_num

theorem v18_large_long_test_0019_step_1 : (1830 : ℤ) = 2 * 660 + 510 := by
  norm_num

theorem v18_large_long_test_0019_step_2 : (660 : ℤ) = 1 * 510 + 150 := by
  norm_num

theorem v18_large_long_test_0019_step_3 : (510 : ℤ) = 3 * 150 + 60 := by
  norm_num

theorem v18_large_long_test_0019_step_4 : (150 : ℤ) = 2 * 60 + 30 := by
  norm_num

theorem v18_large_long_test_0019_step_5 : (60 : ℤ) = 2 * 30 + 0 := by
  norm_num

theorem v18_large_long_test_0019_divides : ¬ (30 : ℤ) ∣ (67 : ℤ) := by
  norm_num

theorem v18_large_long_test_0019_conclusion : ¬ (∃ x y : ℤ, (67 : ℤ) = (1830 : ℤ) * x + (2490 : ℤ) * y) := by
  have hgcd : (Int.gcd (1830 : ℤ) (2490 : ℤ) : ℤ) = 30 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (1830 : ℤ) (2490 : ℤ) (67 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_large_long_test_0019_divides hd

theorem v18_large_long_test_0045_gcd : Nat.gcd 1120 690 = 10 := by
  norm_num [Nat.gcd]

theorem v18_large_long_test_0045_step_0 : (1120 : ℤ) = 1 * 690 + 430 := by
  norm_num

theorem v18_large_long_test_0045_step_1 : (690 : ℤ) = 1 * 430 + 260 := by
  norm_num

theorem v18_large_long_test_0045_step_2 : (430 : ℤ) = 1 * 260 + 170 := by
  norm_num

theorem v18_large_long_test_0045_step_3 : (260 : ℤ) = 1 * 170 + 90 := by
  norm_num

theorem v18_large_long_test_0045_step_4 : (170 : ℤ) = 1 * 90 + 80 := by
  norm_num

theorem v18_large_long_test_0045_step_5 : (90 : ℤ) = 1 * 80 + 10 := by
  norm_num

theorem v18_large_long_test_0045_step_6 : (80 : ℤ) = 8 * 10 + 0 := by
  norm_num

theorem v18_large_long_test_0045_divides : ¬ (10 : ℤ) ∣ (-39 : ℤ) := by
  norm_num

theorem v18_large_long_test_0045_conclusion : ¬ (∃ x y : ℤ, (-39 : ℤ) = (1120 : ℤ) * x + (690 : ℤ) * y) := by
  have hgcd : (Int.gcd (1120 : ℤ) (690 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (1120 : ℤ) (690 : ℤ) (-39 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_large_long_test_0045_divides hd

theorem v18_large_long_test_0046_gcd : Nat.gcd 658 1092 = 14 := by
  norm_num [Nat.gcd]

theorem v18_large_long_test_0046_step_0 : (1092 : ℤ) = 1 * 658 + 434 := by
  norm_num

theorem v18_large_long_test_0046_step_1 : (658 : ℤ) = 1 * 434 + 224 := by
  norm_num

theorem v18_large_long_test_0046_step_2 : (434 : ℤ) = 1 * 224 + 210 := by
  norm_num

theorem v18_large_long_test_0046_step_3 : (224 : ℤ) = 1 * 210 + 14 := by
  norm_num

theorem v18_large_long_test_0046_step_4 : (210 : ℤ) = 15 * 14 + 0 := by
  norm_num

theorem v18_large_long_test_0046_divides : (14 : ℤ) ∣ (-154 : ℤ) := by
  norm_num

theorem v18_large_long_test_0046_conclusion : ∃ x y : ℤ, (-154 : ℤ) = (658 : ℤ) * x + (1092 : ℤ) * y := by
  have hgcd : (Int.gcd (658 : ℤ) (1092 : ℤ) : ℤ) = 14 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (658 : ℤ) (1092 : ℤ) (-154 : ℤ)).2
  simpa [hgcd] using v18_large_long_test_0046_divides

theorem v18_large_long_test_0047_gcd : Nat.gcd 2085 1380 = 15 := by
  norm_num [Nat.gcd]

theorem v18_large_long_test_0047_step_0 : (2085 : ℤ) = 1 * 1380 + 705 := by
  norm_num

theorem v18_large_long_test_0047_step_1 : (1380 : ℤ) = 1 * 705 + 675 := by
  norm_num

theorem v18_large_long_test_0047_step_2 : (705 : ℤ) = 1 * 675 + 30 := by
  norm_num

theorem v18_large_long_test_0047_step_3 : (675 : ℤ) = 22 * 30 + 15 := by
  norm_num

theorem v18_large_long_test_0047_step_4 : (30 : ℤ) = 2 * 15 + 0 := by
  norm_num

theorem v18_large_long_test_0047_divides : ¬ (15 : ℤ) ∣ (-359 : ℤ) := by
  norm_num

theorem v18_large_long_test_0047_conclusion : ¬ (∃ x y : ℤ, (-359 : ℤ) = (2085 : ℤ) * x + (1380 : ℤ) * y) := by
  have hgcd : (Int.gcd (2085 : ℤ) (1380 : ℤ) : ℤ) = 15 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (2085 : ℤ) (1380 : ℤ) (-359 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_large_long_test_0047_divides hd

theorem v18_large_short_test_0023_gcd : Nat.gcd 1075 1125 = 25 := by
  norm_num [Nat.gcd]

theorem v18_large_short_test_0023_step_0 : (1125 : ℤ) = 1 * 1075 + 50 := by
  norm_num

theorem v18_large_short_test_0023_step_1 : (1075 : ℤ) = 21 * 50 + 25 := by
  norm_num

theorem v18_large_short_test_0023_step_2 : (50 : ℤ) = 2 * 25 + 0 := by
  norm_num

theorem v18_large_short_test_0023_divides : ¬ (25 : ℤ) ∣ (-392 : ℤ) := by
  norm_num

theorem v18_large_short_test_0023_conclusion : ¬ (∃ x y : ℤ, (-392 : ℤ) = (1075 : ℤ) * x + (1125 : ℤ) * y) := by
  have hgcd : (Int.gcd (1075 : ℤ) (1125 : ℤ) : ℤ) = 25 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (1075 : ℤ) (1125 : ℤ) (-392 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_large_short_test_0023_divides hd

theorem v18_large_short_test_0032_gcd : Nat.gcd 2175 360 = 15 := by
  norm_num [Nat.gcd]

theorem v18_large_short_test_0032_step_0 : (2175 : ℤ) = 6 * 360 + 15 := by
  norm_num

theorem v18_large_short_test_0032_step_1 : (360 : ℤ) = 24 * 15 + 0 := by
  norm_num

theorem v18_large_short_test_0032_divides : (15 : ℤ) ∣ (255 : ℤ) := by
  norm_num

theorem v18_large_short_test_0032_conclusion : ∃ x y : ℤ, (255 : ℤ) = (2175 : ℤ) * x + (360 : ℤ) * y := by
  have hgcd : (Int.gcd (2175 : ℤ) (360 : ℤ) : ℤ) = 15 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (2175 : ℤ) (360 : ℤ) (255 : ℤ)).2
  simpa [hgcd] using v18_large_short_test_0032_divides

theorem v18_large_short_test_0039_gcd : Nat.gcd 1711 145 = 29 := by
  norm_num [Nat.gcd]

theorem v18_large_short_test_0039_step_0 : (1711 : ℤ) = 11 * 145 + 116 := by
  norm_num

theorem v18_large_short_test_0039_step_1 : (145 : ℤ) = 1 * 116 + 29 := by
  norm_num

theorem v18_large_short_test_0039_step_2 : (116 : ℤ) = 4 * 29 + 0 := by
  norm_num

theorem v18_large_short_test_0039_divides : ¬ (29 : ℤ) ∣ (106 : ℤ) := by
  norm_num

theorem v18_large_short_test_0039_conclusion : ¬ (∃ x y : ℤ, (106 : ℤ) = (1711 : ℤ) * x + (145 : ℤ) * y) := by
  have hgcd : (Int.gcd (1711 : ℤ) (145 : ℤ) : ℤ) = 29 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (1711 : ℤ) (145 : ℤ) (106 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_large_short_test_0039_divides hd

theorem v18_large_short_test_0044_gcd : Nat.gcd 1236 1164 = 12 := by
  norm_num [Nat.gcd]

theorem v18_large_short_test_0044_step_0 : (1236 : ℤ) = 1 * 1164 + 72 := by
  norm_num

theorem v18_large_short_test_0044_step_1 : (1164 : ℤ) = 16 * 72 + 12 := by
  norm_num

theorem v18_large_short_test_0044_step_2 : (72 : ℤ) = 6 * 12 + 0 := by
  norm_num

theorem v18_large_short_test_0044_divides : (12 : ℤ) ∣ (24 : ℤ) := by
  norm_num

theorem v18_large_short_test_0044_conclusion : ∃ x y : ℤ, (24 : ℤ) = (1236 : ℤ) * x + (1164 : ℤ) * y := by
  have hgcd : (Int.gcd (1236 : ℤ) (1164 : ℤ) : ℤ) = 12 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (1236 : ℤ) (1164 : ℤ) (24 : ℤ)).2
  simpa [hgcd] using v18_large_short_test_0044_divides

theorem v18_medium_long_test_0000_gcd : Nat.gcd 510 940 = 10 := by
  norm_num [Nat.gcd]

theorem v18_medium_long_test_0000_step_0 : (940 : ℤ) = 1 * 510 + 430 := by
  norm_num

theorem v18_medium_long_test_0000_step_1 : (510 : ℤ) = 1 * 430 + 80 := by
  norm_num

theorem v18_medium_long_test_0000_step_2 : (430 : ℤ) = 5 * 80 + 30 := by
  norm_num

theorem v18_medium_long_test_0000_step_3 : (80 : ℤ) = 2 * 30 + 20 := by
  norm_num

theorem v18_medium_long_test_0000_step_4 : (30 : ℤ) = 1 * 20 + 10 := by
  norm_num

theorem v18_medium_long_test_0000_step_5 : (20 : ℤ) = 2 * 10 + 0 := by
  norm_num

theorem v18_medium_long_test_0000_divides : (10 : ℤ) ∣ (160 : ℤ) := by
  norm_num

theorem v18_medium_long_test_0000_conclusion : ∃ x y : ℤ, (160 : ℤ) = (510 : ℤ) * x + (940 : ℤ) * y := by
  have hgcd : (Int.gcd (510 : ℤ) (940 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (510 : ℤ) (940 : ℤ) (160 : ℤ)).2
  simpa [hgcd] using v18_medium_long_test_0000_divides

theorem v18_medium_long_test_0006_gcd : Nat.gcd 736 292 = 4 := by
  norm_num [Nat.gcd]

theorem v18_medium_long_test_0006_step_0 : (736 : ℤ) = 2 * 292 + 152 := by
  norm_num

theorem v18_medium_long_test_0006_step_1 : (292 : ℤ) = 1 * 152 + 140 := by
  norm_num

theorem v18_medium_long_test_0006_step_2 : (152 : ℤ) = 1 * 140 + 12 := by
  norm_num

theorem v18_medium_long_test_0006_step_3 : (140 : ℤ) = 11 * 12 + 8 := by
  norm_num

theorem v18_medium_long_test_0006_step_4 : (12 : ℤ) = 1 * 8 + 4 := by
  norm_num

theorem v18_medium_long_test_0006_step_5 : (8 : ℤ) = 2 * 4 + 0 := by
  norm_num

theorem v18_medium_long_test_0006_divides : (4 : ℤ) ∣ (28 : ℤ) := by
  norm_num

theorem v18_medium_long_test_0006_conclusion : ∃ x y : ℤ, (28 : ℤ) = (736 : ℤ) * x + (292 : ℤ) * y := by
  have hgcd : (Int.gcd (736 : ℤ) (292 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (736 : ℤ) (292 : ℤ) (28 : ℤ)).2
  simpa [hgcd] using v18_medium_long_test_0006_divides

theorem v18_medium_long_test_0007_gcd : Nat.gcd 423 729 = 9 := by
  norm_num [Nat.gcd]

theorem v18_medium_long_test_0007_step_0 : (729 : ℤ) = 1 * 423 + 306 := by
  norm_num

theorem v18_medium_long_test_0007_step_1 : (423 : ℤ) = 1 * 306 + 117 := by
  norm_num

theorem v18_medium_long_test_0007_step_2 : (306 : ℤ) = 2 * 117 + 72 := by
  norm_num

theorem v18_medium_long_test_0007_step_3 : (117 : ℤ) = 1 * 72 + 45 := by
  norm_num

theorem v18_medium_long_test_0007_step_4 : (72 : ℤ) = 1 * 45 + 27 := by
  norm_num

theorem v18_medium_long_test_0007_step_5 : (45 : ℤ) = 1 * 27 + 18 := by
  norm_num

theorem v18_medium_long_test_0007_step_6 : (27 : ℤ) = 1 * 18 + 9 := by
  norm_num

theorem v18_medium_long_test_0007_step_7 : (18 : ℤ) = 2 * 9 + 0 := by
  norm_num

theorem v18_medium_long_test_0007_divides : ¬ (9 : ℤ) ∣ (-1 : ℤ) := by
  norm_num

theorem v18_medium_long_test_0007_conclusion : ¬ (∃ x y : ℤ, (-1 : ℤ) = (423 : ℤ) * x + (729 : ℤ) * y) := by
  have hgcd : (Int.gcd (423 : ℤ) (729 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (423 : ℤ) (729 : ℤ) (-1 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_medium_long_test_0007_divides hd

theorem v18_medium_long_test_0019_gcd : Nat.gcd 895 525 = 5 := by
  norm_num [Nat.gcd]

theorem v18_medium_long_test_0019_step_0 : (895 : ℤ) = 1 * 525 + 370 := by
  norm_num

theorem v18_medium_long_test_0019_step_1 : (525 : ℤ) = 1 * 370 + 155 := by
  norm_num

theorem v18_medium_long_test_0019_step_2 : (370 : ℤ) = 2 * 155 + 60 := by
  norm_num

theorem v18_medium_long_test_0019_step_3 : (155 : ℤ) = 2 * 60 + 35 := by
  norm_num

theorem v18_medium_long_test_0019_step_4 : (60 : ℤ) = 1 * 35 + 25 := by
  norm_num

theorem v18_medium_long_test_0019_step_5 : (35 : ℤ) = 1 * 25 + 10 := by
  norm_num

theorem v18_medium_long_test_0019_step_6 : (25 : ℤ) = 2 * 10 + 5 := by
  norm_num

theorem v18_medium_long_test_0019_step_7 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem v18_medium_long_test_0019_divides : ¬ (5 : ℤ) ∣ (-104 : ℤ) := by
  norm_num

theorem v18_medium_long_test_0019_conclusion : ¬ (∃ x y : ℤ, (-104 : ℤ) = (895 : ℤ) * x + (525 : ℤ) * y) := by
  have hgcd : (Int.gcd (895 : ℤ) (525 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (895 : ℤ) (525 : ℤ) (-104 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_medium_long_test_0019_divides hd

theorem v18_medium_long_test_0020_gcd : Nat.gcd 321 630 = 3 := by
  norm_num [Nat.gcd]

theorem v18_medium_long_test_0020_step_0 : (630 : ℤ) = 1 * 321 + 309 := by
  norm_num

theorem v18_medium_long_test_0020_step_1 : (321 : ℤ) = 1 * 309 + 12 := by
  norm_num

theorem v18_medium_long_test_0020_step_2 : (309 : ℤ) = 25 * 12 + 9 := by
  norm_num

theorem v18_medium_long_test_0020_step_3 : (12 : ℤ) = 1 * 9 + 3 := by
  norm_num

theorem v18_medium_long_test_0020_step_4 : (9 : ℤ) = 3 * 3 + 0 := by
  norm_num

theorem v18_medium_long_test_0020_divides : (3 : ℤ) ∣ (36 : ℤ) := by
  norm_num

theorem v18_medium_long_test_0020_conclusion : ∃ x y : ℤ, (36 : ℤ) = (321 : ℤ) * x + (630 : ℤ) * y := by
  have hgcd : (Int.gcd (321 : ℤ) (630 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (321 : ℤ) (630 : ℤ) (36 : ℤ)).2
  simpa [hgcd] using v18_medium_long_test_0020_divides

theorem v18_medium_long_test_0021_gcd : Nat.gcd 915 665 = 5 := by
  norm_num [Nat.gcd]

theorem v18_medium_long_test_0021_step_0 : (915 : ℤ) = 1 * 665 + 250 := by
  norm_num

theorem v18_medium_long_test_0021_step_1 : (665 : ℤ) = 2 * 250 + 165 := by
  norm_num

theorem v18_medium_long_test_0021_step_2 : (250 : ℤ) = 1 * 165 + 85 := by
  norm_num

theorem v18_medium_long_test_0021_step_3 : (165 : ℤ) = 1 * 85 + 80 := by
  norm_num

theorem v18_medium_long_test_0021_step_4 : (85 : ℤ) = 1 * 80 + 5 := by
  norm_num

theorem v18_medium_long_test_0021_step_5 : (80 : ℤ) = 16 * 5 + 0 := by
  norm_num

theorem v18_medium_long_test_0021_divides : ¬ (5 : ℤ) ∣ (-29 : ℤ) := by
  norm_num

theorem v18_medium_long_test_0021_conclusion : ¬ (∃ x y : ℤ, (-29 : ℤ) = (915 : ℤ) * x + (665 : ℤ) * y) := by
  have hgcd : (Int.gcd (915 : ℤ) (665 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (915 : ℤ) (665 : ℤ) (-29 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_medium_long_test_0021_divides hd

theorem v18_medium_long_test_0029_gcd : Nat.gcd 448 720 = 16 := by
  norm_num [Nat.gcd]

theorem v18_medium_long_test_0029_step_0 : (720 : ℤ) = 1 * 448 + 272 := by
  norm_num

theorem v18_medium_long_test_0029_step_1 : (448 : ℤ) = 1 * 272 + 176 := by
  norm_num

theorem v18_medium_long_test_0029_step_2 : (272 : ℤ) = 1 * 176 + 96 := by
  norm_num

theorem v18_medium_long_test_0029_step_3 : (176 : ℤ) = 1 * 96 + 80 := by
  norm_num

theorem v18_medium_long_test_0029_step_4 : (96 : ℤ) = 1 * 80 + 16 := by
  norm_num

theorem v18_medium_long_test_0029_step_5 : (80 : ℤ) = 5 * 16 + 0 := by
  norm_num

theorem v18_medium_long_test_0029_divides : ¬ (16 : ℤ) ∣ (390 : ℤ) := by
  norm_num

theorem v18_medium_long_test_0029_conclusion : ¬ (∃ x y : ℤ, (390 : ℤ) = (448 : ℤ) * x + (720 : ℤ) * y) := by
  have hgcd : (Int.gcd (448 : ℤ) (720 : ℤ) : ℤ) = 16 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (448 : ℤ) (720 : ℤ) (390 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_medium_long_test_0029_divides hd

theorem v18_medium_long_test_0034_gcd : Nat.gcd 369 624 = 3 := by
  norm_num [Nat.gcd]

theorem v18_medium_long_test_0034_step_0 : (624 : ℤ) = 1 * 369 + 255 := by
  norm_num

theorem v18_medium_long_test_0034_step_1 : (369 : ℤ) = 1 * 255 + 114 := by
  norm_num

theorem v18_medium_long_test_0034_step_2 : (255 : ℤ) = 2 * 114 + 27 := by
  norm_num

theorem v18_medium_long_test_0034_step_3 : (114 : ℤ) = 4 * 27 + 6 := by
  norm_num

theorem v18_medium_long_test_0034_step_4 : (27 : ℤ) = 4 * 6 + 3 := by
  norm_num

theorem v18_medium_long_test_0034_step_5 : (6 : ℤ) = 2 * 3 + 0 := by
  norm_num

theorem v18_medium_long_test_0034_divides : (3 : ℤ) ∣ (69 : ℤ) := by
  norm_num

theorem v18_medium_long_test_0034_conclusion : ∃ x y : ℤ, (69 : ℤ) = (369 : ℤ) * x + (624 : ℤ) * y := by
  have hgcd : (Int.gcd (369 : ℤ) (624 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (369 : ℤ) (624 : ℤ) (69 : ℤ)).2
  simpa [hgcd] using v18_medium_long_test_0034_divides

theorem v18_medium_long_test_0037_gcd : Nat.gcd 800 625 = 25 := by
  norm_num [Nat.gcd]

theorem v18_medium_long_test_0037_step_0 : (800 : ℤ) = 1 * 625 + 175 := by
  norm_num

theorem v18_medium_long_test_0037_step_1 : (625 : ℤ) = 3 * 175 + 100 := by
  norm_num

theorem v18_medium_long_test_0037_step_2 : (175 : ℤ) = 1 * 100 + 75 := by
  norm_num

theorem v18_medium_long_test_0037_step_3 : (100 : ℤ) = 1 * 75 + 25 := by
  norm_num

theorem v18_medium_long_test_0037_step_4 : (75 : ℤ) = 3 * 25 + 0 := by
  norm_num

theorem v18_medium_long_test_0037_divides : ¬ (25 : ℤ) ∣ (-323 : ℤ) := by
  norm_num

theorem v18_medium_long_test_0037_conclusion : ¬ (∃ x y : ℤ, (-323 : ℤ) = (800 : ℤ) * x + (625 : ℤ) * y) := by
  have hgcd : (Int.gcd (800 : ℤ) (625 : ℤ) : ℤ) = 25 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (800 : ℤ) (625 : ℤ) (-323 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_medium_long_test_0037_divides hd

theorem v18_medium_long_test_0048_gcd : Nat.gcd 558 228 = 6 := by
  norm_num [Nat.gcd]

theorem v18_medium_long_test_0048_step_0 : (558 : ℤ) = 2 * 228 + 102 := by
  norm_num

theorem v18_medium_long_test_0048_step_1 : (228 : ℤ) = 2 * 102 + 24 := by
  norm_num

theorem v18_medium_long_test_0048_step_2 : (102 : ℤ) = 4 * 24 + 6 := by
  norm_num

theorem v18_medium_long_test_0048_step_3 : (24 : ℤ) = 4 * 6 + 0 := by
  norm_num

theorem v18_medium_long_test_0048_divides : (6 : ℤ) ∣ (-126 : ℤ) := by
  norm_num

theorem v18_medium_long_test_0048_conclusion : ∃ x y : ℤ, (-126 : ℤ) = (558 : ℤ) * x + (228 : ℤ) * y := by
  have hgcd : (Int.gcd (558 : ℤ) (228 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (558 : ℤ) (228 : ℤ) (-126 : ℤ)).2
  simpa [hgcd] using v18_medium_long_test_0048_divides

theorem v18_medium_short_test_0005_gcd : Nat.gcd 132 638 = 22 := by
  norm_num [Nat.gcd]

theorem v18_medium_short_test_0005_step_0 : (638 : ℤ) = 4 * 132 + 110 := by
  norm_num

theorem v18_medium_short_test_0005_step_1 : (132 : ℤ) = 1 * 110 + 22 := by
  norm_num

theorem v18_medium_short_test_0005_step_2 : (110 : ℤ) = 5 * 22 + 0 := by
  norm_num

theorem v18_medium_short_test_0005_divides : ¬ (22 : ℤ) ∣ (-139 : ℤ) := by
  norm_num

theorem v18_medium_short_test_0005_conclusion : ¬ (∃ x y : ℤ, (-139 : ℤ) = (132 : ℤ) * x + (638 : ℤ) * y) := by
  have hgcd : (Int.gcd (132 : ℤ) (638 : ℤ) : ℤ) = 22 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (132 : ℤ) (638 : ℤ) (-139 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_medium_short_test_0005_divides hd

theorem v18_medium_short_test_0006_gcd : Nat.gcd 836 342 = 38 := by
  norm_num [Nat.gcd]

theorem v18_medium_short_test_0006_step_0 : (836 : ℤ) = 2 * 342 + 152 := by
  norm_num

theorem v18_medium_short_test_0006_step_1 : (342 : ℤ) = 2 * 152 + 38 := by
  norm_num

theorem v18_medium_short_test_0006_step_2 : (152 : ℤ) = 4 * 38 + 0 := by
  norm_num

theorem v18_medium_short_test_0006_divides : (38 : ℤ) ∣ (-646 : ℤ) := by
  norm_num

theorem v18_medium_short_test_0006_conclusion : ∃ x y : ℤ, (-646 : ℤ) = (836 : ℤ) * x + (342 : ℤ) * y := by
  have hgcd : (Int.gcd (836 : ℤ) (342 : ℤ) : ℤ) = 38 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (836 : ℤ) (342 : ℤ) (-646 : ℤ)).2
  simpa [hgcd] using v18_medium_short_test_0006_divides

theorem v18_medium_short_test_0008_gcd : Nat.gcd 792 798 = 6 := by
  norm_num [Nat.gcd]

theorem v18_medium_short_test_0008_step_0 : (798 : ℤ) = 1 * 792 + 6 := by
  norm_num

theorem v18_medium_short_test_0008_step_1 : (792 : ℤ) = 132 * 6 + 0 := by
  norm_num

theorem v18_medium_short_test_0008_divides : (6 : ℤ) ∣ (120 : ℤ) := by
  norm_num

theorem v18_medium_short_test_0008_conclusion : ∃ x y : ℤ, (120 : ℤ) = (792 : ℤ) * x + (798 : ℤ) * y := by
  have hgcd : (Int.gcd (792 : ℤ) (798 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (792 : ℤ) (798 : ℤ) (120 : ℤ)).2
  simpa [hgcd] using v18_medium_short_test_0008_divides

theorem v18_medium_short_test_0012_gcd : Nat.gcd 890 870 = 10 := by
  norm_num [Nat.gcd]

theorem v18_medium_short_test_0012_step_0 : (890 : ℤ) = 1 * 870 + 20 := by
  norm_num

theorem v18_medium_short_test_0012_step_1 : (870 : ℤ) = 43 * 20 + 10 := by
  norm_num

theorem v18_medium_short_test_0012_step_2 : (20 : ℤ) = 2 * 10 + 0 := by
  norm_num

theorem v18_medium_short_test_0012_divides : (10 : ℤ) ∣ (120 : ℤ) := by
  norm_num

theorem v18_medium_short_test_0012_conclusion : ∃ x y : ℤ, (120 : ℤ) = (890 : ℤ) * x + (870 : ℤ) * y := by
  have hgcd : (Int.gcd (890 : ℤ) (870 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (890 : ℤ) (870 : ℤ) (120 : ℤ)).2
  simpa [hgcd] using v18_medium_short_test_0012_divides

theorem v18_medium_short_test_0013_gcd : Nat.gcd 716 64 = 4 := by
  norm_num [Nat.gcd]

theorem v18_medium_short_test_0013_step_0 : (716 : ℤ) = 11 * 64 + 12 := by
  norm_num

theorem v18_medium_short_test_0013_step_1 : (64 : ℤ) = 5 * 12 + 4 := by
  norm_num

theorem v18_medium_short_test_0013_step_2 : (12 : ℤ) = 3 * 4 + 0 := by
  norm_num

theorem v18_medium_short_test_0013_divides : ¬ (4 : ℤ) ∣ (-6 : ℤ) := by
  norm_num

theorem v18_medium_short_test_0013_conclusion : ¬ (∃ x y : ℤ, (-6 : ℤ) = (716 : ℤ) * x + (64 : ℤ) * y) := by
  have hgcd : (Int.gcd (716 : ℤ) (64 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (716 : ℤ) (64 : ℤ) (-6 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_medium_short_test_0013_divides hd

theorem v18_medium_short_test_0014_gcd : Nat.gcd 763 385 = 7 := by
  norm_num [Nat.gcd]

theorem v18_medium_short_test_0014_step_0 : (763 : ℤ) = 1 * 385 + 378 := by
  norm_num

theorem v18_medium_short_test_0014_step_1 : (385 : ℤ) = 1 * 378 + 7 := by
  norm_num

theorem v18_medium_short_test_0014_step_2 : (378 : ℤ) = 54 * 7 + 0 := by
  norm_num

theorem v18_medium_short_test_0014_divides : (7 : ℤ) ∣ (-105 : ℤ) := by
  norm_num

theorem v18_medium_short_test_0014_conclusion : ∃ x y : ℤ, (-105 : ℤ) = (763 : ℤ) * x + (385 : ℤ) * y := by
  have hgcd : (Int.gcd (763 : ℤ) (385 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (763 : ℤ) (385 : ℤ) (-105 : ℤ)).2
  simpa [hgcd] using v18_medium_short_test_0014_divides

theorem v18_medium_short_test_0023_gcd : Nat.gcd 640 15 = 5 := by
  norm_num [Nat.gcd]

theorem v18_medium_short_test_0023_step_0 : (640 : ℤ) = 42 * 15 + 10 := by
  norm_num

theorem v18_medium_short_test_0023_step_1 : (15 : ℤ) = 1 * 10 + 5 := by
  norm_num

theorem v18_medium_short_test_0023_step_2 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem v18_medium_short_test_0023_divides : ¬ (5 : ℤ) ∣ (9 : ℤ) := by
  norm_num

theorem v18_medium_short_test_0023_conclusion : ¬ (∃ x y : ℤ, (9 : ℤ) = (640 : ℤ) * x + (15 : ℤ) * y) := by
  have hgcd : (Int.gcd (640 : ℤ) (15 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (640 : ℤ) (15 : ℤ) (9 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_medium_short_test_0023_divides hd

theorem v18_medium_short_test_0034_gcd : Nat.gcd 534 558 = 6 := by
  norm_num [Nat.gcd]

theorem v18_medium_short_test_0034_step_0 : (558 : ℤ) = 1 * 534 + 24 := by
  norm_num

theorem v18_medium_short_test_0034_step_1 : (534 : ℤ) = 22 * 24 + 6 := by
  norm_num

theorem v18_medium_short_test_0034_step_2 : (24 : ℤ) = 4 * 6 + 0 := by
  norm_num

theorem v18_medium_short_test_0034_divides : (6 : ℤ) ∣ (-126 : ℤ) := by
  norm_num

theorem v18_medium_short_test_0034_conclusion : ∃ x y : ℤ, (-126 : ℤ) = (534 : ℤ) * x + (558 : ℤ) * y := by
  have hgcd : (Int.gcd (534 : ℤ) (558 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (534 : ℤ) (558 : ℤ) (-126 : ℤ)).2
  simpa [hgcd] using v18_medium_short_test_0034_divides

theorem v18_medium_short_test_0038_gcd : Nat.gcd 290 880 = 10 := by
  norm_num [Nat.gcd]

theorem v18_medium_short_test_0038_step_0 : (880 : ℤ) = 3 * 290 + 10 := by
  norm_num

theorem v18_medium_short_test_0038_step_1 : (290 : ℤ) = 29 * 10 + 0 := by
  norm_num

theorem v18_medium_short_test_0038_divides : (10 : ℤ) ∣ (-90 : ℤ) := by
  norm_num

theorem v18_medium_short_test_0038_conclusion : ∃ x y : ℤ, (-90 : ℤ) = (290 : ℤ) * x + (880 : ℤ) * y := by
  have hgcd : (Int.gcd (290 : ℤ) (880 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (290 : ℤ) (880 : ℤ) (-90 : ℤ)).2
  simpa [hgcd] using v18_medium_short_test_0038_divides

theorem v18_medium_short_test_0047_gcd : Nat.gcd 400 930 = 10 := by
  norm_num [Nat.gcd]

theorem v18_medium_short_test_0047_step_0 : (930 : ℤ) = 2 * 400 + 130 := by
  norm_num

theorem v18_medium_short_test_0047_step_1 : (400 : ℤ) = 3 * 130 + 10 := by
  norm_num

theorem v18_medium_short_test_0047_step_2 : (130 : ℤ) = 13 * 10 + 0 := by
  norm_num

theorem v18_medium_short_test_0047_divides : ¬ (10 : ℤ) ∣ (-87 : ℤ) := by
  norm_num

theorem v18_medium_short_test_0047_conclusion : ¬ (∃ x y : ℤ, (-87 : ℤ) = (400 : ℤ) * x + (930 : ℤ) * y) := by
  have hgcd : (Int.gcd (400 : ℤ) (930 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (400 : ℤ) (930 : ℤ) (-87 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_medium_short_test_0047_divides hd

theorem v18_small_long_test_0001_gcd : Nat.gcd 57 105 = 3 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0001_step_0 : (105 : ℤ) = 1 * 57 + 48 := by
  norm_num

theorem v18_small_long_test_0001_step_1 : (57 : ℤ) = 1 * 48 + 9 := by
  norm_num

theorem v18_small_long_test_0001_step_2 : (48 : ℤ) = 5 * 9 + 3 := by
  norm_num

theorem v18_small_long_test_0001_step_3 : (9 : ℤ) = 3 * 3 + 0 := by
  norm_num

theorem v18_small_long_test_0001_divides : ¬ (3 : ℤ) ∣ (19 : ℤ) := by
  norm_num

theorem v18_small_long_test_0001_conclusion : ¬ (∃ x y : ℤ, (19 : ℤ) = (57 : ℤ) * x + (105 : ℤ) * y) := by
  have hgcd : (Int.gcd (57 : ℤ) (105 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (57 : ℤ) (105 : ℤ) (19 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_long_test_0001_divides hd

theorem v18_small_long_test_0005_gcd : Nat.gcd 147 81 = 3 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0005_step_0 : (147 : ℤ) = 1 * 81 + 66 := by
  norm_num

theorem v18_small_long_test_0005_step_1 : (81 : ℤ) = 1 * 66 + 15 := by
  norm_num

theorem v18_small_long_test_0005_step_2 : (66 : ℤ) = 4 * 15 + 6 := by
  norm_num

theorem v18_small_long_test_0005_step_3 : (15 : ℤ) = 2 * 6 + 3 := by
  norm_num

theorem v18_small_long_test_0005_step_4 : (6 : ℤ) = 2 * 3 + 0 := by
  norm_num

theorem v18_small_long_test_0005_divides : ¬ (3 : ℤ) ∣ (-1 : ℤ) := by
  norm_num

theorem v18_small_long_test_0005_conclusion : ¬ (∃ x y : ℤ, (-1 : ℤ) = (147 : ℤ) * x + (81 : ℤ) * y) := by
  have hgcd : (Int.gcd (147 : ℤ) (81 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (147 : ℤ) (81 : ℤ) (-1 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_long_test_0005_divides hd

theorem v18_small_long_test_0006_gcd : Nat.gcd 165 190 = 5 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0006_step_0 : (190 : ℤ) = 1 * 165 + 25 := by
  norm_num

theorem v18_small_long_test_0006_step_1 : (165 : ℤ) = 6 * 25 + 15 := by
  norm_num

theorem v18_small_long_test_0006_step_2 : (25 : ℤ) = 1 * 15 + 10 := by
  norm_num

theorem v18_small_long_test_0006_step_3 : (15 : ℤ) = 1 * 10 + 5 := by
  norm_num

theorem v18_small_long_test_0006_step_4 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem v18_small_long_test_0006_divides : (5 : ℤ) ∣ (-65 : ℤ) := by
  norm_num

theorem v18_small_long_test_0006_conclusion : ∃ x y : ℤ, (-65 : ℤ) = (165 : ℤ) * x + (190 : ℤ) * y := by
  have hgcd : (Int.gcd (165 : ℤ) (190 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (165 : ℤ) (190 : ℤ) (-65 : ℤ)).2
  simpa [hgcd] using v18_small_long_test_0006_divides

theorem v18_small_long_test_0007_gcd : Nat.gcd 87 198 = 3 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0007_step_0 : (198 : ℤ) = 2 * 87 + 24 := by
  norm_num

theorem v18_small_long_test_0007_step_1 : (87 : ℤ) = 3 * 24 + 15 := by
  norm_num

theorem v18_small_long_test_0007_step_2 : (24 : ℤ) = 1 * 15 + 9 := by
  norm_num

theorem v18_small_long_test_0007_step_3 : (15 : ℤ) = 1 * 9 + 6 := by
  norm_num

theorem v18_small_long_test_0007_step_4 : (9 : ℤ) = 1 * 6 + 3 := by
  norm_num

theorem v18_small_long_test_0007_step_5 : (6 : ℤ) = 2 * 3 + 0 := by
  norm_num

theorem v18_small_long_test_0007_divides : ¬ (3 : ℤ) ∣ (26 : ℤ) := by
  norm_num

theorem v18_small_long_test_0007_conclusion : ¬ (∃ x y : ℤ, (26 : ℤ) = (87 : ℤ) * x + (198 : ℤ) * y) := by
  have hgcd : (Int.gcd (87 : ℤ) (198 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (87 : ℤ) (198 : ℤ) (26 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_long_test_0007_divides hd

theorem v18_small_long_test_0009_gcd : Nat.gcd 123 207 = 3 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0009_step_0 : (207 : ℤ) = 1 * 123 + 84 := by
  norm_num

theorem v18_small_long_test_0009_step_1 : (123 : ℤ) = 1 * 84 + 39 := by
  norm_num

theorem v18_small_long_test_0009_step_2 : (84 : ℤ) = 2 * 39 + 6 := by
  norm_num

theorem v18_small_long_test_0009_step_3 : (39 : ℤ) = 6 * 6 + 3 := by
  norm_num

theorem v18_small_long_test_0009_step_4 : (6 : ℤ) = 2 * 3 + 0 := by
  norm_num

theorem v18_small_long_test_0009_divides : ¬ (3 : ℤ) ∣ (25 : ℤ) := by
  norm_num

theorem v18_small_long_test_0009_conclusion : ¬ (∃ x y : ℤ, (25 : ℤ) = (123 : ℤ) * x + (207 : ℤ) * y) := by
  have hgcd : (Int.gcd (123 : ℤ) (207 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (123 : ℤ) (207 : ℤ) (25 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_long_test_0009_divides hd

theorem v18_small_long_test_0010_gcd : Nat.gcd 86 164 = 2 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0010_step_0 : (164 : ℤ) = 1 * 86 + 78 := by
  norm_num

theorem v18_small_long_test_0010_step_1 : (86 : ℤ) = 1 * 78 + 8 := by
  norm_num

theorem v18_small_long_test_0010_step_2 : (78 : ℤ) = 9 * 8 + 6 := by
  norm_num

theorem v18_small_long_test_0010_step_3 : (8 : ℤ) = 1 * 6 + 2 := by
  norm_num

theorem v18_small_long_test_0010_step_4 : (6 : ℤ) = 3 * 2 + 0 := by
  norm_num

theorem v18_small_long_test_0010_divides : (2 : ℤ) ∣ (-36 : ℤ) := by
  norm_num

theorem v18_small_long_test_0010_conclusion : ∃ x y : ℤ, (-36 : ℤ) = (86 : ℤ) * x + (164 : ℤ) * y := by
  have hgcd : (Int.gcd (86 : ℤ) (164 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (86 : ℤ) (164 : ℤ) (-36 : ℤ)).2
  simpa [hgcd] using v18_small_long_test_0010_divides

theorem v18_small_long_test_0011_gcd : Nat.gcd 194 84 = 2 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0011_step_0 : (194 : ℤ) = 2 * 84 + 26 := by
  norm_num

theorem v18_small_long_test_0011_step_1 : (84 : ℤ) = 3 * 26 + 6 := by
  norm_num

theorem v18_small_long_test_0011_step_2 : (26 : ℤ) = 4 * 6 + 2 := by
  norm_num

theorem v18_small_long_test_0011_step_3 : (6 : ℤ) = 3 * 2 + 0 := by
  norm_num

theorem v18_small_long_test_0011_divides : ¬ (2 : ℤ) ∣ (15 : ℤ) := by
  norm_num

theorem v18_small_long_test_0011_conclusion : ¬ (∃ x y : ℤ, (15 : ℤ) = (194 : ℤ) * x + (84 : ℤ) * y) := by
  have hgcd : (Int.gcd (194 : ℤ) (84 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (194 : ℤ) (84 : ℤ) (15 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_long_test_0011_divides hd

theorem v18_small_long_test_0012_gcd : Nat.gcd 189 161 = 7 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0012_step_0 : (189 : ℤ) = 1 * 161 + 28 := by
  norm_num

theorem v18_small_long_test_0012_step_1 : (161 : ℤ) = 5 * 28 + 21 := by
  norm_num

theorem v18_small_long_test_0012_step_2 : (28 : ℤ) = 1 * 21 + 7 := by
  norm_num

theorem v18_small_long_test_0012_step_3 : (21 : ℤ) = 3 * 7 + 0 := by
  norm_num

theorem v18_small_long_test_0012_divides : (7 : ℤ) ∣ (147 : ℤ) := by
  norm_num

theorem v18_small_long_test_0012_conclusion : ∃ x y : ℤ, (147 : ℤ) = (189 : ℤ) * x + (161 : ℤ) * y := by
  have hgcd : (Int.gcd (189 : ℤ) (161 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (189 : ℤ) (161 : ℤ) (147 : ℤ)).2
  simpa [hgcd] using v18_small_long_test_0012_divides

theorem v18_small_long_test_0016_gcd : Nat.gcd 50 64 = 2 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0016_step_0 : (64 : ℤ) = 1 * 50 + 14 := by
  norm_num

theorem v18_small_long_test_0016_step_1 : (50 : ℤ) = 3 * 14 + 8 := by
  norm_num

theorem v18_small_long_test_0016_step_2 : (14 : ℤ) = 1 * 8 + 6 := by
  norm_num

theorem v18_small_long_test_0016_step_3 : (8 : ℤ) = 1 * 6 + 2 := by
  norm_num

theorem v18_small_long_test_0016_step_4 : (6 : ℤ) = 3 * 2 + 0 := by
  norm_num

theorem v18_small_long_test_0016_divides : (2 : ℤ) ∣ (-50 : ℤ) := by
  norm_num

theorem v18_small_long_test_0016_conclusion : ∃ x y : ℤ, (-50 : ℤ) = (50 : ℤ) * x + (64 : ℤ) * y := by
  have hgcd : (Int.gcd (50 : ℤ) (64 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (50 : ℤ) (64 : ℤ) (-50 : ℤ)).2
  simpa [hgcd] using v18_small_long_test_0016_divides

theorem v18_small_long_test_0019_gcd : Nat.gcd 129 81 = 3 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0019_step_0 : (129 : ℤ) = 1 * 81 + 48 := by
  norm_num

theorem v18_small_long_test_0019_step_1 : (81 : ℤ) = 1 * 48 + 33 := by
  norm_num

theorem v18_small_long_test_0019_step_2 : (48 : ℤ) = 1 * 33 + 15 := by
  norm_num

theorem v18_small_long_test_0019_step_3 : (33 : ℤ) = 2 * 15 + 3 := by
  norm_num

theorem v18_small_long_test_0019_step_4 : (15 : ℤ) = 5 * 3 + 0 := by
  norm_num

theorem v18_small_long_test_0019_divides : ¬ (3 : ℤ) ∣ (74 : ℤ) := by
  norm_num

theorem v18_small_long_test_0019_conclusion : ¬ (∃ x y : ℤ, (74 : ℤ) = (129 : ℤ) * x + (81 : ℤ) * y) := by
  have hgcd : (Int.gcd (129 : ℤ) (81 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (129 : ℤ) (81 : ℤ) (74 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_long_test_0019_divides hd

theorem v18_small_long_test_0020_gcd : Nat.gcd 100 144 = 4 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0020_step_0 : (144 : ℤ) = 1 * 100 + 44 := by
  norm_num

theorem v18_small_long_test_0020_step_1 : (100 : ℤ) = 2 * 44 + 12 := by
  norm_num

theorem v18_small_long_test_0020_step_2 : (44 : ℤ) = 3 * 12 + 8 := by
  norm_num

theorem v18_small_long_test_0020_step_3 : (12 : ℤ) = 1 * 8 + 4 := by
  norm_num

theorem v18_small_long_test_0020_step_4 : (8 : ℤ) = 2 * 4 + 0 := by
  norm_num

theorem v18_small_long_test_0020_divides : (4 : ℤ) ∣ (88 : ℤ) := by
  norm_num

theorem v18_small_long_test_0020_conclusion : ∃ x y : ℤ, (88 : ℤ) = (100 : ℤ) * x + (144 : ℤ) * y := by
  have hgcd : (Int.gcd (100 : ℤ) (144 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (100 : ℤ) (144 : ℤ) (88 : ℤ)).2
  simpa [hgcd] using v18_small_long_test_0020_divides

theorem v18_small_long_test_0021_gcd : Nat.gcd 142 192 = 2 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0021_step_0 : (192 : ℤ) = 1 * 142 + 50 := by
  norm_num

theorem v18_small_long_test_0021_step_1 : (142 : ℤ) = 2 * 50 + 42 := by
  norm_num

theorem v18_small_long_test_0021_step_2 : (50 : ℤ) = 1 * 42 + 8 := by
  norm_num

theorem v18_small_long_test_0021_step_3 : (42 : ℤ) = 5 * 8 + 2 := by
  norm_num

theorem v18_small_long_test_0021_step_4 : (8 : ℤ) = 4 * 2 + 0 := by
  norm_num

theorem v18_small_long_test_0021_divides : ¬ (2 : ℤ) ∣ (13 : ℤ) := by
  norm_num

theorem v18_small_long_test_0021_conclusion : ¬ (∃ x y : ℤ, (13 : ℤ) = (142 : ℤ) * x + (192 : ℤ) * y) := by
  have hgcd : (Int.gcd (142 : ℤ) (192 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (142 : ℤ) (192 : ℤ) (13 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_long_test_0021_divides hd

theorem v18_small_long_test_0023_gcd : Nat.gcd 192 141 = 3 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0023_step_0 : (192 : ℤ) = 1 * 141 + 51 := by
  norm_num

theorem v18_small_long_test_0023_step_1 : (141 : ℤ) = 2 * 51 + 39 := by
  norm_num

theorem v18_small_long_test_0023_step_2 : (51 : ℤ) = 1 * 39 + 12 := by
  norm_num

theorem v18_small_long_test_0023_step_3 : (39 : ℤ) = 3 * 12 + 3 := by
  norm_num

theorem v18_small_long_test_0023_step_4 : (12 : ℤ) = 4 * 3 + 0 := by
  norm_num

theorem v18_small_long_test_0023_divides : ¬ (3 : ℤ) ∣ (-5 : ℤ) := by
  norm_num

theorem v18_small_long_test_0023_conclusion : ¬ (∃ x y : ℤ, (-5 : ℤ) = (192 : ℤ) * x + (141 : ℤ) * y) := by
  have hgcd : (Int.gcd (192 : ℤ) (141 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (192 : ℤ) (141 : ℤ) (-5 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_long_test_0023_divides hd

theorem v18_small_long_test_0024_gcd : Nat.gcd 135 40 = 5 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0024_step_0 : (135 : ℤ) = 3 * 40 + 15 := by
  norm_num

theorem v18_small_long_test_0024_step_1 : (40 : ℤ) = 2 * 15 + 10 := by
  norm_num

theorem v18_small_long_test_0024_step_2 : (15 : ℤ) = 1 * 10 + 5 := by
  norm_num

theorem v18_small_long_test_0024_step_3 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem v18_small_long_test_0024_divides : (5 : ℤ) ∣ (40 : ℤ) := by
  norm_num

theorem v18_small_long_test_0024_conclusion : ∃ x y : ℤ, (40 : ℤ) = (135 : ℤ) * x + (40 : ℤ) * y := by
  have hgcd : (Int.gcd (135 : ℤ) (40 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (135 : ℤ) (40 : ℤ) (40 : ℤ)).2
  simpa [hgcd] using v18_small_long_test_0024_divides

theorem v18_small_long_test_0025_gcd : Nat.gcd 122 172 = 2 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0025_step_0 : (172 : ℤ) = 1 * 122 + 50 := by
  norm_num

theorem v18_small_long_test_0025_step_1 : (122 : ℤ) = 2 * 50 + 22 := by
  norm_num

theorem v18_small_long_test_0025_step_2 : (50 : ℤ) = 2 * 22 + 6 := by
  norm_num

theorem v18_small_long_test_0025_step_3 : (22 : ℤ) = 3 * 6 + 4 := by
  norm_num

theorem v18_small_long_test_0025_step_4 : (6 : ℤ) = 1 * 4 + 2 := by
  norm_num

theorem v18_small_long_test_0025_step_5 : (4 : ℤ) = 2 * 2 + 0 := by
  norm_num

theorem v18_small_long_test_0025_divides : ¬ (2 : ℤ) ∣ (47 : ℤ) := by
  norm_num

theorem v18_small_long_test_0025_conclusion : ¬ (∃ x y : ℤ, (47 : ℤ) = (122 : ℤ) * x + (172 : ℤ) * y) := by
  have hgcd : (Int.gcd (122 : ℤ) (172 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (122 : ℤ) (172 : ℤ) (47 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_long_test_0025_divides hd

theorem v18_small_long_test_0026_gcd : Nat.gcd 156 56 = 4 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0026_step_0 : (156 : ℤ) = 2 * 56 + 44 := by
  norm_num

theorem v18_small_long_test_0026_step_1 : (56 : ℤ) = 1 * 44 + 12 := by
  norm_num

theorem v18_small_long_test_0026_step_2 : (44 : ℤ) = 3 * 12 + 8 := by
  norm_num

theorem v18_small_long_test_0026_step_3 : (12 : ℤ) = 1 * 8 + 4 := by
  norm_num

theorem v18_small_long_test_0026_step_4 : (8 : ℤ) = 2 * 4 + 0 := by
  norm_num

theorem v18_small_long_test_0026_divides : (4 : ℤ) ∣ (56 : ℤ) := by
  norm_num

theorem v18_small_long_test_0026_conclusion : ∃ x y : ℤ, (56 : ℤ) = (156 : ℤ) * x + (56 : ℤ) * y := by
  have hgcd : (Int.gcd (156 : ℤ) (56 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (156 : ℤ) (56 : ℤ) (56 : ℤ)).2
  simpa [hgcd] using v18_small_long_test_0026_divides

theorem v18_small_long_test_0029_gcd : Nat.gcd 70 202 = 2 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0029_step_0 : (202 : ℤ) = 2 * 70 + 62 := by
  norm_num

theorem v18_small_long_test_0029_step_1 : (70 : ℤ) = 1 * 62 + 8 := by
  norm_num

theorem v18_small_long_test_0029_step_2 : (62 : ℤ) = 7 * 8 + 6 := by
  norm_num

theorem v18_small_long_test_0029_step_3 : (8 : ℤ) = 1 * 6 + 2 := by
  norm_num

theorem v18_small_long_test_0029_step_4 : (6 : ℤ) = 3 * 2 + 0 := by
  norm_num

theorem v18_small_long_test_0029_divides : ¬ (2 : ℤ) ∣ (-37 : ℤ) := by
  norm_num

theorem v18_small_long_test_0029_conclusion : ¬ (∃ x y : ℤ, (-37 : ℤ) = (70 : ℤ) * x + (202 : ℤ) * y) := by
  have hgcd : (Int.gcd (70 : ℤ) (202 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (70 : ℤ) (202 : ℤ) (-37 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_long_test_0029_divides hd

theorem v18_small_long_test_0030_gcd : Nat.gcd 138 81 = 3 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0030_step_0 : (138 : ℤ) = 1 * 81 + 57 := by
  norm_num

theorem v18_small_long_test_0030_step_1 : (81 : ℤ) = 1 * 57 + 24 := by
  norm_num

theorem v18_small_long_test_0030_step_2 : (57 : ℤ) = 2 * 24 + 9 := by
  norm_num

theorem v18_small_long_test_0030_step_3 : (24 : ℤ) = 2 * 9 + 6 := by
  norm_num

theorem v18_small_long_test_0030_step_4 : (9 : ℤ) = 1 * 6 + 3 := by
  norm_num

theorem v18_small_long_test_0030_step_5 : (6 : ℤ) = 2 * 3 + 0 := by
  norm_num

theorem v18_small_long_test_0030_divides : (3 : ℤ) ∣ (-9 : ℤ) := by
  norm_num

theorem v18_small_long_test_0030_conclusion : ∃ x y : ℤ, (-9 : ℤ) = (138 : ℤ) * x + (81 : ℤ) * y := by
  have hgcd : (Int.gcd (138 : ℤ) (81 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (138 : ℤ) (81 : ℤ) (-9 : ℤ)).2
  simpa [hgcd] using v18_small_long_test_0030_divides

theorem v18_small_long_test_0033_gcd : Nat.gcd 92 216 = 4 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0033_step_0 : (216 : ℤ) = 2 * 92 + 32 := by
  norm_num

theorem v18_small_long_test_0033_step_1 : (92 : ℤ) = 2 * 32 + 28 := by
  norm_num

theorem v18_small_long_test_0033_step_2 : (32 : ℤ) = 1 * 28 + 4 := by
  norm_num

theorem v18_small_long_test_0033_step_3 : (28 : ℤ) = 7 * 4 + 0 := by
  norm_num

theorem v18_small_long_test_0033_divides : ¬ (4 : ℤ) ∣ (58 : ℤ) := by
  norm_num

theorem v18_small_long_test_0033_conclusion : ¬ (∃ x y : ℤ, (58 : ℤ) = (92 : ℤ) * x + (216 : ℤ) * y) := by
  have hgcd : (Int.gcd (92 : ℤ) (216 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (92 : ℤ) (216 : ℤ) (58 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_long_test_0033_divides hd

theorem v18_small_long_test_0036_gcd : Nat.gcd 60 141 = 3 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0036_step_0 : (141 : ℤ) = 2 * 60 + 21 := by
  norm_num

theorem v18_small_long_test_0036_step_1 : (60 : ℤ) = 2 * 21 + 18 := by
  norm_num

theorem v18_small_long_test_0036_step_2 : (21 : ℤ) = 1 * 18 + 3 := by
  norm_num

theorem v18_small_long_test_0036_step_3 : (18 : ℤ) = 6 * 3 + 0 := by
  norm_num

theorem v18_small_long_test_0036_divides : (3 : ℤ) ∣ (-63 : ℤ) := by
  norm_num

theorem v18_small_long_test_0036_conclusion : ∃ x y : ℤ, (-63 : ℤ) = (60 : ℤ) * x + (141 : ℤ) * y := by
  have hgcd : (Int.gcd (60 : ℤ) (141 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (60 : ℤ) (141 : ℤ) (-63 : ℤ)).2
  simpa [hgcd] using v18_small_long_test_0036_divides

theorem v18_small_long_test_0037_gcd : Nat.gcd 154 100 = 2 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0037_step_0 : (154 : ℤ) = 1 * 100 + 54 := by
  norm_num

theorem v18_small_long_test_0037_step_1 : (100 : ℤ) = 1 * 54 + 46 := by
  norm_num

theorem v18_small_long_test_0037_step_2 : (54 : ℤ) = 1 * 46 + 8 := by
  norm_num

theorem v18_small_long_test_0037_step_3 : (46 : ℤ) = 5 * 8 + 6 := by
  norm_num

theorem v18_small_long_test_0037_step_4 : (8 : ℤ) = 1 * 6 + 2 := by
  norm_num

theorem v18_small_long_test_0037_step_5 : (6 : ℤ) = 3 * 2 + 0 := by
  norm_num

theorem v18_small_long_test_0037_divides : ¬ (2 : ℤ) ∣ (23 : ℤ) := by
  norm_num

theorem v18_small_long_test_0037_conclusion : ¬ (∃ x y : ℤ, (23 : ℤ) = (154 : ℤ) * x + (100 : ℤ) * y) := by
  have hgcd : (Int.gcd (154 : ℤ) (100 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (154 : ℤ) (100 : ℤ) (23 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_long_test_0037_divides hd

theorem v18_small_long_test_0038_gcd : Nat.gcd 78 45 = 3 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0038_step_0 : (78 : ℤ) = 1 * 45 + 33 := by
  norm_num

theorem v18_small_long_test_0038_step_1 : (45 : ℤ) = 1 * 33 + 12 := by
  norm_num

theorem v18_small_long_test_0038_step_2 : (33 : ℤ) = 2 * 12 + 9 := by
  norm_num

theorem v18_small_long_test_0038_step_3 : (12 : ℤ) = 1 * 9 + 3 := by
  norm_num

theorem v18_small_long_test_0038_step_4 : (9 : ℤ) = 3 * 3 + 0 := by
  norm_num

theorem v18_small_long_test_0038_divides : (3 : ℤ) ∣ (-36 : ℤ) := by
  norm_num

theorem v18_small_long_test_0038_conclusion : ∃ x y : ℤ, (-36 : ℤ) = (78 : ℤ) * x + (45 : ℤ) * y := by
  have hgcd : (Int.gcd (78 : ℤ) (45 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (78 : ℤ) (45 : ℤ) (-36 : ℤ)).2
  simpa [hgcd] using v18_small_long_test_0038_divides

theorem v18_small_long_test_0039_gcd : Nat.gcd 120 14 = 2 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0039_step_0 : (120 : ℤ) = 8 * 14 + 8 := by
  norm_num

theorem v18_small_long_test_0039_step_1 : (14 : ℤ) = 1 * 8 + 6 := by
  norm_num

theorem v18_small_long_test_0039_step_2 : (8 : ℤ) = 1 * 6 + 2 := by
  norm_num

theorem v18_small_long_test_0039_step_3 : (6 : ℤ) = 3 * 2 + 0 := by
  norm_num

theorem v18_small_long_test_0039_divides : ¬ (2 : ℤ) ∣ (33 : ℤ) := by
  norm_num

theorem v18_small_long_test_0039_conclusion : ¬ (∃ x y : ℤ, (33 : ℤ) = (120 : ℤ) * x + (14 : ℤ) * y) := by
  have hgcd : (Int.gcd (120 : ℤ) (14 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (120 : ℤ) (14 : ℤ) (33 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_long_test_0039_divides hd

theorem v18_small_long_test_0040_gcd : Nat.gcd 66 93 = 3 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0040_step_0 : (93 : ℤ) = 1 * 66 + 27 := by
  norm_num

theorem v18_small_long_test_0040_step_1 : (66 : ℤ) = 2 * 27 + 12 := by
  norm_num

theorem v18_small_long_test_0040_step_2 : (27 : ℤ) = 2 * 12 + 3 := by
  norm_num

theorem v18_small_long_test_0040_step_3 : (12 : ℤ) = 4 * 3 + 0 := by
  norm_num

theorem v18_small_long_test_0040_divides : (3 : ℤ) ∣ (-6 : ℤ) := by
  norm_num

theorem v18_small_long_test_0040_conclusion : ∃ x y : ℤ, (-6 : ℤ) = (66 : ℤ) * x + (93 : ℤ) * y := by
  have hgcd : (Int.gcd (66 : ℤ) (93 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (66 : ℤ) (93 : ℤ) (-6 : ℤ)).2
  simpa [hgcd] using v18_small_long_test_0040_divides

theorem v18_small_long_test_0041_gcd : Nat.gcd 135 186 = 3 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0041_step_0 : (186 : ℤ) = 1 * 135 + 51 := by
  norm_num

theorem v18_small_long_test_0041_step_1 : (135 : ℤ) = 2 * 51 + 33 := by
  norm_num

theorem v18_small_long_test_0041_step_2 : (51 : ℤ) = 1 * 33 + 18 := by
  norm_num

theorem v18_small_long_test_0041_step_3 : (33 : ℤ) = 1 * 18 + 15 := by
  norm_num

theorem v18_small_long_test_0041_step_4 : (18 : ℤ) = 1 * 15 + 3 := by
  norm_num

theorem v18_small_long_test_0041_step_5 : (15 : ℤ) = 5 * 3 + 0 := by
  norm_num

theorem v18_small_long_test_0041_divides : ¬ (3 : ℤ) ∣ (64 : ℤ) := by
  norm_num

theorem v18_small_long_test_0041_conclusion : ¬ (∃ x y : ℤ, (64 : ℤ) = (135 : ℤ) * x + (186 : ℤ) * y) := by
  have hgcd : (Int.gcd (135 : ℤ) (186 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (135 : ℤ) (186 : ℤ) (64 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_long_test_0041_divides hd

theorem v18_small_long_test_0042_gcd : Nat.gcd 210 144 = 6 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0042_step_0 : (210 : ℤ) = 1 * 144 + 66 := by
  norm_num

theorem v18_small_long_test_0042_step_1 : (144 : ℤ) = 2 * 66 + 12 := by
  norm_num

theorem v18_small_long_test_0042_step_2 : (66 : ℤ) = 5 * 12 + 6 := by
  norm_num

theorem v18_small_long_test_0042_step_3 : (12 : ℤ) = 2 * 6 + 0 := by
  norm_num

theorem v18_small_long_test_0042_divides : (6 : ℤ) ∣ (138 : ℤ) := by
  norm_num

theorem v18_small_long_test_0042_conclusion : ∃ x y : ℤ, (138 : ℤ) = (210 : ℤ) * x + (144 : ℤ) * y := by
  have hgcd : (Int.gcd (210 : ℤ) (144 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (210 : ℤ) (144 : ℤ) (138 : ℤ)).2
  simpa [hgcd] using v18_small_long_test_0042_divides

theorem v18_small_long_test_0044_gcd : Nat.gcd 38 108 = 2 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0044_step_0 : (108 : ℤ) = 2 * 38 + 32 := by
  norm_num

theorem v18_small_long_test_0044_step_1 : (38 : ℤ) = 1 * 32 + 6 := by
  norm_num

theorem v18_small_long_test_0044_step_2 : (32 : ℤ) = 5 * 6 + 2 := by
  norm_num

theorem v18_small_long_test_0044_step_3 : (6 : ℤ) = 3 * 2 + 0 := by
  norm_num

theorem v18_small_long_test_0044_divides : (2 : ℤ) ∣ (44 : ℤ) := by
  norm_num

theorem v18_small_long_test_0044_conclusion : ∃ x y : ℤ, (44 : ℤ) = (38 : ℤ) * x + (108 : ℤ) * y := by
  have hgcd : (Int.gcd (38 : ℤ) (108 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (38 : ℤ) (108 : ℤ) (44 : ℤ)).2
  simpa [hgcd] using v18_small_long_test_0044_divides

theorem v18_small_long_test_0047_gcd : Nat.gcd 106 182 = 2 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0047_step_0 : (182 : ℤ) = 1 * 106 + 76 := by
  norm_num

theorem v18_small_long_test_0047_step_1 : (106 : ℤ) = 1 * 76 + 30 := by
  norm_num

theorem v18_small_long_test_0047_step_2 : (76 : ℤ) = 2 * 30 + 16 := by
  norm_num

theorem v18_small_long_test_0047_step_3 : (30 : ℤ) = 1 * 16 + 14 := by
  norm_num

theorem v18_small_long_test_0047_step_4 : (16 : ℤ) = 1 * 14 + 2 := by
  norm_num

theorem v18_small_long_test_0047_step_5 : (14 : ℤ) = 7 * 2 + 0 := by
  norm_num

theorem v18_small_long_test_0047_divides : ¬ (2 : ℤ) ∣ (-33 : ℤ) := by
  norm_num

theorem v18_small_long_test_0047_conclusion : ¬ (∃ x y : ℤ, (-33 : ℤ) = (106 : ℤ) * x + (182 : ℤ) * y) := by
  have hgcd : (Int.gcd (106 : ℤ) (182 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (106 : ℤ) (182 : ℤ) (-33 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_long_test_0047_divides hd

theorem v18_small_long_test_0049_gcd : Nat.gcd 95 130 = 5 := by
  norm_num [Nat.gcd]

theorem v18_small_long_test_0049_step_0 : (130 : ℤ) = 1 * 95 + 35 := by
  norm_num

theorem v18_small_long_test_0049_step_1 : (95 : ℤ) = 2 * 35 + 25 := by
  norm_num

theorem v18_small_long_test_0049_step_2 : (35 : ℤ) = 1 * 25 + 10 := by
  norm_num

theorem v18_small_long_test_0049_step_3 : (25 : ℤ) = 2 * 10 + 5 := by
  norm_num

theorem v18_small_long_test_0049_step_4 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem v18_small_long_test_0049_divides : ¬ (5 : ℤ) ∣ (-78 : ℤ) := by
  norm_num

theorem v18_small_long_test_0049_conclusion : ¬ (∃ x y : ℤ, (-78 : ℤ) = (95 : ℤ) * x + (130 : ℤ) * y) := by
  have hgcd : (Int.gcd (95 : ℤ) (130 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (95 : ℤ) (130 : ℤ) (-78 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_long_test_0049_divides hd

theorem v18_small_short_test_0000_gcd : Nat.gcd 4 202 = 2 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0000_step_0 : (202 : ℤ) = 50 * 4 + 2 := by
  norm_num

theorem v18_small_short_test_0000_step_1 : (4 : ℤ) = 2 * 2 + 0 := by
  norm_num

theorem v18_small_short_test_0000_divides : (2 : ℤ) ∣ (-10 : ℤ) := by
  norm_num

theorem v18_small_short_test_0000_conclusion : ∃ x y : ℤ, (-10 : ℤ) = (4 : ℤ) * x + (202 : ℤ) * y := by
  have hgcd : (Int.gcd (4 : ℤ) (202 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (4 : ℤ) (202 : ℤ) (-10 : ℤ)).2
  simpa [hgcd] using v18_small_short_test_0000_divides

theorem v18_small_short_test_0001_gcd : Nat.gcd 120 129 = 3 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0001_step_0 : (129 : ℤ) = 1 * 120 + 9 := by
  norm_num

theorem v18_small_short_test_0001_step_1 : (120 : ℤ) = 13 * 9 + 3 := by
  norm_num

theorem v18_small_short_test_0001_step_2 : (9 : ℤ) = 3 * 3 + 0 := by
  norm_num

theorem v18_small_short_test_0001_divides : ¬ (3 : ℤ) ∣ (50 : ℤ) := by
  norm_num

theorem v18_small_short_test_0001_conclusion : ¬ (∃ x y : ℤ, (50 : ℤ) = (120 : ℤ) * x + (129 : ℤ) * y) := by
  have hgcd : (Int.gcd (120 : ℤ) (129 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (120 : ℤ) (129 : ℤ) (50 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_short_test_0001_divides hd

theorem v18_small_short_test_0002_gcd : Nat.gcd 50 110 = 10 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0002_step_0 : (110 : ℤ) = 2 * 50 + 10 := by
  norm_num

theorem v18_small_short_test_0002_step_1 : (50 : ℤ) = 5 * 10 + 0 := by
  norm_num

theorem v18_small_short_test_0002_divides : (10 : ℤ) ∣ (110 : ℤ) := by
  norm_num

theorem v18_small_short_test_0002_conclusion : ∃ x y : ℤ, (110 : ℤ) = (50 : ℤ) * x + (110 : ℤ) * y := by
  have hgcd : (Int.gcd (50 : ℤ) (110 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (50 : ℤ) (110 : ℤ) (110 : ℤ)).2
  simpa [hgcd] using v18_small_short_test_0002_divides

theorem v18_small_short_test_0006_gcd : Nat.gcd 99 132 = 33 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0006_step_0 : (132 : ℤ) = 1 * 99 + 33 := by
  norm_num

theorem v18_small_short_test_0006_step_1 : (99 : ℤ) = 3 * 33 + 0 := by
  norm_num

theorem v18_small_short_test_0006_divides : (33 : ℤ) ∣ (-297 : ℤ) := by
  norm_num

theorem v18_small_short_test_0006_conclusion : ∃ x y : ℤ, (-297 : ℤ) = (99 : ℤ) * x + (132 : ℤ) * y := by
  have hgcd : (Int.gcd (99 : ℤ) (132 : ℤ) : ℤ) = 33 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (99 : ℤ) (132 : ℤ) (-297 : ℤ)).2
  simpa [hgcd] using v18_small_short_test_0006_divides

theorem v18_small_short_test_0008_gcd : Nat.gcd 143 77 = 11 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0008_step_0 : (143 : ℤ) = 1 * 77 + 66 := by
  norm_num

theorem v18_small_short_test_0008_step_1 : (77 : ℤ) = 1 * 66 + 11 := by
  norm_num

theorem v18_small_short_test_0008_step_2 : (66 : ℤ) = 6 * 11 + 0 := by
  norm_num

theorem v18_small_short_test_0008_divides : (11 : ℤ) ∣ (-143 : ℤ) := by
  norm_num

theorem v18_small_short_test_0008_conclusion : ∃ x y : ℤ, (-143 : ℤ) = (143 : ℤ) * x + (77 : ℤ) * y := by
  have hgcd : (Int.gcd (143 : ℤ) (77 : ℤ) : ℤ) = 11 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (143 : ℤ) (77 : ℤ) (-143 : ℤ)).2
  simpa [hgcd] using v18_small_short_test_0008_divides

theorem v18_small_short_test_0009_gcd : Nat.gcd 66 75 = 3 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0009_step_0 : (75 : ℤ) = 1 * 66 + 9 := by
  norm_num

theorem v18_small_short_test_0009_step_1 : (66 : ℤ) = 7 * 9 + 3 := by
  norm_num

theorem v18_small_short_test_0009_step_2 : (9 : ℤ) = 3 * 3 + 0 := by
  norm_num

theorem v18_small_short_test_0009_divides : ¬ (3 : ℤ) ∣ (73 : ℤ) := by
  norm_num

theorem v18_small_short_test_0009_conclusion : ¬ (∃ x y : ℤ, (73 : ℤ) = (66 : ℤ) * x + (75 : ℤ) * y) := by
  have hgcd : (Int.gcd (66 : ℤ) (75 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (66 : ℤ) (75 : ℤ) (73 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_short_test_0009_divides hd

theorem v18_small_short_test_0010_gcd : Nat.gcd 24 66 = 6 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0010_step_0 : (66 : ℤ) = 2 * 24 + 18 := by
  norm_num

theorem v18_small_short_test_0010_step_1 : (24 : ℤ) = 1 * 18 + 6 := by
  norm_num

theorem v18_small_short_test_0010_step_2 : (18 : ℤ) = 3 * 6 + 0 := by
  norm_num

theorem v18_small_short_test_0010_divides : (6 : ℤ) ∣ (-78 : ℤ) := by
  norm_num

theorem v18_small_short_test_0010_conclusion : ∃ x y : ℤ, (-78 : ℤ) = (24 : ℤ) * x + (66 : ℤ) * y := by
  have hgcd : (Int.gcd (24 : ℤ) (66 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (24 : ℤ) (66 : ℤ) (-78 : ℤ)).2
  simpa [hgcd] using v18_small_short_test_0010_divides

theorem v18_small_short_test_0011_gcd : Nat.gcd 75 84 = 3 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0011_step_0 : (84 : ℤ) = 1 * 75 + 9 := by
  norm_num

theorem v18_small_short_test_0011_step_1 : (75 : ℤ) = 8 * 9 + 3 := by
  norm_num

theorem v18_small_short_test_0011_step_2 : (9 : ℤ) = 3 * 3 + 0 := by
  norm_num

theorem v18_small_short_test_0011_divides : ¬ (3 : ℤ) ∣ (-59 : ℤ) := by
  norm_num

theorem v18_small_short_test_0011_conclusion : ¬ (∃ x y : ℤ, (-59 : ℤ) = (75 : ℤ) * x + (84 : ℤ) * y) := by
  have hgcd : (Int.gcd (75 : ℤ) (84 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (75 : ℤ) (84 : ℤ) (-59 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_short_test_0011_divides hd

theorem v18_small_short_test_0013_gcd : Nat.gcd 136 152 = 8 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0013_step_0 : (152 : ℤ) = 1 * 136 + 16 := by
  norm_num

theorem v18_small_short_test_0013_step_1 : (136 : ℤ) = 8 * 16 + 8 := by
  norm_num

theorem v18_small_short_test_0013_step_2 : (16 : ℤ) = 2 * 8 + 0 := by
  norm_num

theorem v18_small_short_test_0013_divides : ¬ (8 : ℤ) ∣ (74 : ℤ) := by
  norm_num

theorem v18_small_short_test_0013_conclusion : ¬ (∃ x y : ℤ, (74 : ℤ) = (136 : ℤ) * x + (152 : ℤ) * y) := by
  have hgcd : (Int.gcd (136 : ℤ) (152 : ℤ) : ℤ) = 8 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (136 : ℤ) (152 : ℤ) (74 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_short_test_0013_divides hd

theorem v18_small_short_test_0015_gcd : Nat.gcd 161 49 = 7 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0015_step_0 : (161 : ℤ) = 3 * 49 + 14 := by
  norm_num

theorem v18_small_short_test_0015_step_1 : (49 : ℤ) = 3 * 14 + 7 := by
  norm_num

theorem v18_small_short_test_0015_step_2 : (14 : ℤ) = 2 * 7 + 0 := by
  norm_num

theorem v18_small_short_test_0015_divides : ¬ (7 : ℤ) ∣ (-136 : ℤ) := by
  norm_num

theorem v18_small_short_test_0015_conclusion : ¬ (∃ x y : ℤ, (-136 : ℤ) = (161 : ℤ) * x + (49 : ℤ) * y) := by
  have hgcd : (Int.gcd (161 : ℤ) (49 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (161 : ℤ) (49 : ℤ) (-136 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_short_test_0015_divides hd

theorem v18_small_short_test_0016_gcd : Nat.gcd 95 10 = 5 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0016_step_0 : (95 : ℤ) = 9 * 10 + 5 := by
  norm_num

theorem v18_small_short_test_0016_step_1 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem v18_small_short_test_0016_divides : (5 : ℤ) ∣ (10 : ℤ) := by
  norm_num

theorem v18_small_short_test_0016_conclusion : ∃ x y : ℤ, (10 : ℤ) = (95 : ℤ) * x + (10 : ℤ) * y := by
  have hgcd : (Int.gcd (95 : ℤ) (10 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (95 : ℤ) (10 : ℤ) (10 : ℤ)).2
  simpa [hgcd] using v18_small_short_test_0016_divides

theorem v18_small_short_test_0017_gcd : Nat.gcd 120 129 = 3 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0017_step_0 : (129 : ℤ) = 1 * 120 + 9 := by
  norm_num

theorem v18_small_short_test_0017_step_1 : (120 : ℤ) = 13 * 9 + 3 := by
  norm_num

theorem v18_small_short_test_0017_step_2 : (9 : ℤ) = 3 * 3 + 0 := by
  norm_num

theorem v18_small_short_test_0017_divides : ¬ (3 : ℤ) ∣ (-25 : ℤ) := by
  norm_num

theorem v18_small_short_test_0017_conclusion : ¬ (∃ x y : ℤ, (-25 : ℤ) = (120 : ℤ) * x + (129 : ℤ) * y) := by
  have hgcd : (Int.gcd (120 : ℤ) (129 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (120 : ℤ) (129 : ℤ) (-25 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_short_test_0017_divides hd

theorem v18_small_short_test_0018_gcd : Nat.gcd 158 170 = 2 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0018_step_0 : (170 : ℤ) = 1 * 158 + 12 := by
  norm_num

theorem v18_small_short_test_0018_step_1 : (158 : ℤ) = 13 * 12 + 2 := by
  norm_num

theorem v18_small_short_test_0018_step_2 : (12 : ℤ) = 6 * 2 + 0 := by
  norm_num

theorem v18_small_short_test_0018_divides : (2 : ℤ) ∣ (34 : ℤ) := by
  norm_num

theorem v18_small_short_test_0018_conclusion : ∃ x y : ℤ, (34 : ℤ) = (158 : ℤ) * x + (170 : ℤ) * y := by
  have hgcd : (Int.gcd (158 : ℤ) (170 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (158 : ℤ) (170 : ℤ) (34 : ℤ)).2
  simpa [hgcd] using v18_small_short_test_0018_divides

theorem v18_small_short_test_0019_gcd : Nat.gcd 201 15 = 3 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0019_step_0 : (201 : ℤ) = 13 * 15 + 6 := by
  norm_num

theorem v18_small_short_test_0019_step_1 : (15 : ℤ) = 2 * 6 + 3 := by
  norm_num

theorem v18_small_short_test_0019_step_2 : (6 : ℤ) = 2 * 3 + 0 := by
  norm_num

theorem v18_small_short_test_0019_divides : ¬ (3 : ℤ) ∣ (55 : ℤ) := by
  norm_num

theorem v18_small_short_test_0019_conclusion : ¬ (∃ x y : ℤ, (55 : ℤ) = (201 : ℤ) * x + (15 : ℤ) * y) := by
  have hgcd : (Int.gcd (201 : ℤ) (15 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (201 : ℤ) (15 : ℤ) (55 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_short_test_0019_divides hd

theorem v18_small_short_test_0020_gcd : Nat.gcd 207 21 = 3 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0020_step_0 : (207 : ℤ) = 9 * 21 + 18 := by
  norm_num

theorem v18_small_short_test_0020_step_1 : (21 : ℤ) = 1 * 18 + 3 := by
  norm_num

theorem v18_small_short_test_0020_step_2 : (18 : ℤ) = 6 * 3 + 0 := by
  norm_num

theorem v18_small_short_test_0020_divides : (3 : ℤ) ∣ (-63 : ℤ) := by
  norm_num

theorem v18_small_short_test_0020_conclusion : ∃ x y : ℤ, (-63 : ℤ) = (207 : ℤ) * x + (21 : ℤ) * y := by
  have hgcd : (Int.gcd (207 : ℤ) (21 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (207 : ℤ) (21 : ℤ) (-63 : ℤ)).2
  simpa [hgcd] using v18_small_short_test_0020_divides

theorem v18_small_short_test_0022_gcd : Nat.gcd 128 144 = 16 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0022_step_0 : (144 : ℤ) = 1 * 128 + 16 := by
  norm_num

theorem v18_small_short_test_0022_step_1 : (128 : ℤ) = 8 * 16 + 0 := by
  norm_num

theorem v18_small_short_test_0022_divides : (16 : ℤ) ∣ (384 : ℤ) := by
  norm_num

theorem v18_small_short_test_0022_conclusion : ∃ x y : ℤ, (384 : ℤ) = (128 : ℤ) * x + (144 : ℤ) * y := by
  have hgcd : (Int.gcd (128 : ℤ) (144 : ℤ) : ℤ) = 16 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (128 : ℤ) (144 : ℤ) (384 : ℤ)).2
  simpa [hgcd] using v18_small_short_test_0022_divides

theorem v18_small_short_test_0023_gcd : Nat.gcd 63 35 = 7 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0023_step_0 : (63 : ℤ) = 1 * 35 + 28 := by
  norm_num

theorem v18_small_short_test_0023_step_1 : (35 : ℤ) = 1 * 28 + 7 := by
  norm_num

theorem v18_small_short_test_0023_step_2 : (28 : ℤ) = 4 * 7 + 0 := by
  norm_num

theorem v18_small_short_test_0023_divides : ¬ (7 : ℤ) ∣ (55 : ℤ) := by
  norm_num

theorem v18_small_short_test_0023_conclusion : ¬ (∃ x y : ℤ, (55 : ℤ) = (63 : ℤ) * x + (35 : ℤ) * y) := by
  have hgcd : (Int.gcd (63 : ℤ) (35 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (63 : ℤ) (35 : ℤ) (55 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_short_test_0023_divides hd

theorem v18_small_short_test_0025_gcd : Nat.gcd 66 121 = 11 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0025_step_0 : (121 : ℤ) = 1 * 66 + 55 := by
  norm_num

theorem v18_small_short_test_0025_step_1 : (66 : ℤ) = 1 * 55 + 11 := by
  norm_num

theorem v18_small_short_test_0025_step_2 : (55 : ℤ) = 5 * 11 + 0 := by
  norm_num

theorem v18_small_short_test_0025_divides : ¬ (11 : ℤ) ∣ (116 : ℤ) := by
  norm_num

theorem v18_small_short_test_0025_conclusion : ¬ (∃ x y : ℤ, (116 : ℤ) = (66 : ℤ) * x + (121 : ℤ) * y) := by
  have hgcd : (Int.gcd (66 : ℤ) (121 : ℤ) : ℤ) = 11 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (66 : ℤ) (121 : ℤ) (116 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_short_test_0025_divides hd

theorem v18_small_short_test_0026_gcd : Nat.gcd 15 65 = 5 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0026_step_0 : (65 : ℤ) = 4 * 15 + 5 := by
  norm_num

theorem v18_small_short_test_0026_step_1 : (15 : ℤ) = 3 * 5 + 0 := by
  norm_num

theorem v18_small_short_test_0026_divides : (5 : ℤ) ∣ (-75 : ℤ) := by
  norm_num

theorem v18_small_short_test_0026_conclusion : ∃ x y : ℤ, (-75 : ℤ) = (15 : ℤ) * x + (65 : ℤ) * y := by
  have hgcd : (Int.gcd (15 : ℤ) (65 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (15 : ℤ) (65 : ℤ) (-75 : ℤ)).2
  simpa [hgcd] using v18_small_short_test_0026_divides

theorem v18_small_short_test_0028_gcd : Nat.gcd 20 164 = 4 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0028_step_0 : (164 : ℤ) = 8 * 20 + 4 := by
  norm_num

theorem v18_small_short_test_0028_step_1 : (20 : ℤ) = 5 * 4 + 0 := by
  norm_num

theorem v18_small_short_test_0028_divides : (4 : ℤ) ∣ (-16 : ℤ) := by
  norm_num

theorem v18_small_short_test_0028_conclusion : ∃ x y : ℤ, (-16 : ℤ) = (20 : ℤ) * x + (164 : ℤ) * y := by
  have hgcd : (Int.gcd (20 : ℤ) (164 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (20 : ℤ) (164 : ℤ) (-16 : ℤ)).2
  simpa [hgcd] using v18_small_short_test_0028_divides

theorem v18_small_short_test_0029_gcd : Nat.gcd 164 160 = 4 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0029_step_0 : (164 : ℤ) = 1 * 160 + 4 := by
  norm_num

theorem v18_small_short_test_0029_step_1 : (160 : ℤ) = 40 * 4 + 0 := by
  norm_num

theorem v18_small_short_test_0029_divides : ¬ (4 : ℤ) ∣ (-90 : ℤ) := by
  norm_num

theorem v18_small_short_test_0029_conclusion : ¬ (∃ x y : ℤ, (-90 : ℤ) = (164 : ℤ) * x + (160 : ℤ) * y) := by
  have hgcd : (Int.gcd (164 : ℤ) (160 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (164 : ℤ) (160 : ℤ) (-90 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_short_test_0029_divides hd

theorem v18_small_short_test_0031_gcd : Nat.gcd 72 96 = 24 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0031_step_0 : (96 : ℤ) = 1 * 72 + 24 := by
  norm_num

theorem v18_small_short_test_0031_step_1 : (72 : ℤ) = 3 * 24 + 0 := by
  norm_num

theorem v18_small_short_test_0031_divides : ¬ (24 : ℤ) ∣ (-43 : ℤ) := by
  norm_num

theorem v18_small_short_test_0031_conclusion : ¬ (∃ x y : ℤ, (-43 : ℤ) = (72 : ℤ) * x + (96 : ℤ) * y) := by
  have hgcd : (Int.gcd (72 : ℤ) (96 : ℤ) : ℤ) = 24 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (72 : ℤ) (96 : ℤ) (-43 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_short_test_0031_divides hd

theorem v18_small_short_test_0032_gcd : Nat.gcd 187 66 = 11 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0032_step_0 : (187 : ℤ) = 2 * 66 + 55 := by
  norm_num

theorem v18_small_short_test_0032_step_1 : (66 : ℤ) = 1 * 55 + 11 := by
  norm_num

theorem v18_small_short_test_0032_step_2 : (55 : ℤ) = 5 * 11 + 0 := by
  norm_num

theorem v18_small_short_test_0032_divides : (11 : ℤ) ∣ (132 : ℤ) := by
  norm_num

theorem v18_small_short_test_0032_conclusion : ∃ x y : ℤ, (132 : ℤ) = (187 : ℤ) * x + (66 : ℤ) * y := by
  have hgcd : (Int.gcd (187 : ℤ) (66 : ℤ) : ℤ) = 11 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (187 : ℤ) (66 : ℤ) (132 : ℤ)).2
  simpa [hgcd] using v18_small_short_test_0032_divides

theorem v18_small_short_test_0033_gcd : Nat.gcd 60 192 = 12 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0033_step_0 : (192 : ℤ) = 3 * 60 + 12 := by
  norm_num

theorem v18_small_short_test_0033_step_1 : (60 : ℤ) = 5 * 12 + 0 := by
  norm_num

theorem v18_small_short_test_0033_divides : ¬ (12 : ℤ) ∣ (87 : ℤ) := by
  norm_num

theorem v18_small_short_test_0033_conclusion : ¬ (∃ x y : ℤ, (87 : ℤ) = (60 : ℤ) * x + (192 : ℤ) * y) := by
  have hgcd : (Int.gcd (60 : ℤ) (192 : ℤ) : ℤ) = 12 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (60 : ℤ) (192 : ℤ) (87 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_short_test_0033_divides hd

theorem v18_small_short_test_0034_gcd : Nat.gcd 200 168 = 8 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0034_step_0 : (200 : ℤ) = 1 * 168 + 32 := by
  norm_num

theorem v18_small_short_test_0034_step_1 : (168 : ℤ) = 5 * 32 + 8 := by
  norm_num

theorem v18_small_short_test_0034_step_2 : (32 : ℤ) = 4 * 8 + 0 := by
  norm_num

theorem v18_small_short_test_0034_divides : (8 : ℤ) ∣ (-136 : ℤ) := by
  norm_num

theorem v18_small_short_test_0034_conclusion : ∃ x y : ℤ, (-136 : ℤ) = (200 : ℤ) * x + (168 : ℤ) * y := by
  have hgcd : (Int.gcd (200 : ℤ) (168 : ℤ) : ℤ) = 8 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (200 : ℤ) (168 : ℤ) (-136 : ℤ)).2
  simpa [hgcd] using v18_small_short_test_0034_divides

theorem v18_small_short_test_0036_gcd : Nat.gcd 204 206 = 2 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0036_step_0 : (206 : ℤ) = 1 * 204 + 2 := by
  norm_num

theorem v18_small_short_test_0036_step_1 : (204 : ℤ) = 102 * 2 + 0 := by
  norm_num

theorem v18_small_short_test_0036_divides : (2 : ℤ) ∣ (-2 : ℤ) := by
  norm_num

theorem v18_small_short_test_0036_conclusion : ∃ x y : ℤ, (-2 : ℤ) = (204 : ℤ) * x + (206 : ℤ) * y := by
  have hgcd : (Int.gcd (204 : ℤ) (206 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (204 : ℤ) (206 : ℤ) (-2 : ℤ)).2
  simpa [hgcd] using v18_small_short_test_0036_divides

theorem v18_small_short_test_0040_gcd : Nat.gcd 72 76 = 4 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0040_step_0 : (76 : ℤ) = 1 * 72 + 4 := by
  norm_num

theorem v18_small_short_test_0040_step_1 : (72 : ℤ) = 18 * 4 + 0 := by
  norm_num

theorem v18_small_short_test_0040_divides : (4 : ℤ) ∣ (-32 : ℤ) := by
  norm_num

theorem v18_small_short_test_0040_conclusion : ∃ x y : ℤ, (-32 : ℤ) = (72 : ℤ) * x + (76 : ℤ) * y := by
  have hgcd : (Int.gcd (72 : ℤ) (76 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (72 : ℤ) (76 : ℤ) (-32 : ℤ)).2
  simpa [hgcd] using v18_small_short_test_0040_divides

theorem v18_small_short_test_0042_gcd : Nat.gcd 195 150 = 15 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0042_step_0 : (195 : ℤ) = 1 * 150 + 45 := by
  norm_num

theorem v18_small_short_test_0042_step_1 : (150 : ℤ) = 3 * 45 + 15 := by
  norm_num

theorem v18_small_short_test_0042_step_2 : (45 : ℤ) = 3 * 15 + 0 := by
  norm_num

theorem v18_small_short_test_0042_divides : (15 : ℤ) ∣ (-165 : ℤ) := by
  norm_num

theorem v18_small_short_test_0042_conclusion : ∃ x y : ℤ, (-165 : ℤ) = (195 : ℤ) * x + (150 : ℤ) * y := by
  have hgcd : (Int.gcd (195 : ℤ) (150 : ℤ) : ℤ) = 15 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (195 : ℤ) (150 : ℤ) (-165 : ℤ)).2
  simpa [hgcd] using v18_small_short_test_0042_divides

theorem v18_small_short_test_0043_gcd : Nat.gcd 138 129 = 3 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0043_step_0 : (138 : ℤ) = 1 * 129 + 9 := by
  norm_num

theorem v18_small_short_test_0043_step_1 : (129 : ℤ) = 14 * 9 + 3 := by
  norm_num

theorem v18_small_short_test_0043_step_2 : (9 : ℤ) = 3 * 3 + 0 := by
  norm_num

theorem v18_small_short_test_0043_divides : ¬ (3 : ℤ) ∣ (-7 : ℤ) := by
  norm_num

theorem v18_small_short_test_0043_conclusion : ¬ (∃ x y : ℤ, (-7 : ℤ) = (138 : ℤ) * x + (129 : ℤ) * y) := by
  have hgcd : (Int.gcd (138 : ℤ) (129 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (138 : ℤ) (129 : ℤ) (-7 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_short_test_0043_divides hd

theorem v18_small_short_test_0044_gcd : Nat.gcd 63 45 = 9 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0044_step_0 : (63 : ℤ) = 1 * 45 + 18 := by
  norm_num

theorem v18_small_short_test_0044_step_1 : (45 : ℤ) = 2 * 18 + 9 := by
  norm_num

theorem v18_small_short_test_0044_step_2 : (18 : ℤ) = 2 * 9 + 0 := by
  norm_num

theorem v18_small_short_test_0044_divides : (9 : ℤ) ∣ (99 : ℤ) := by
  norm_num

theorem v18_small_short_test_0044_conclusion : ∃ x y : ℤ, (99 : ℤ) = (63 : ℤ) * x + (45 : ℤ) * y := by
  have hgcd : (Int.gcd (63 : ℤ) (45 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (63 : ℤ) (45 : ℤ) (99 : ℤ)).2
  simpa [hgcd] using v18_small_short_test_0044_divides

theorem v18_small_short_test_0045_gcd : Nat.gcd 172 144 = 4 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0045_step_0 : (172 : ℤ) = 1 * 144 + 28 := by
  norm_num

theorem v18_small_short_test_0045_step_1 : (144 : ℤ) = 5 * 28 + 4 := by
  norm_num

theorem v18_small_short_test_0045_step_2 : (28 : ℤ) = 7 * 4 + 0 := by
  norm_num

theorem v18_small_short_test_0045_divides : ¬ (4 : ℤ) ∣ (-1 : ℤ) := by
  norm_num

theorem v18_small_short_test_0045_conclusion : ¬ (∃ x y : ℤ, (-1 : ℤ) = (172 : ℤ) * x + (144 : ℤ) * y) := by
  have hgcd : (Int.gcd (172 : ℤ) (144 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (172 : ℤ) (144 : ℤ) (-1 : ℤ)).1 h
  rw [hgcd] at hd
  exact v18_small_short_test_0045_divides hd

theorem v18_small_short_test_0048_gcd : Nat.gcd 128 96 = 32 := by
  norm_num [Nat.gcd]

theorem v18_small_short_test_0048_step_0 : (128 : ℤ) = 1 * 96 + 32 := by
  norm_num

theorem v18_small_short_test_0048_step_1 : (96 : ℤ) = 3 * 32 + 0 := by
  norm_num

theorem v18_small_short_test_0048_divides : (32 : ℤ) ∣ (544 : ℤ) := by
  norm_num

theorem v18_small_short_test_0048_conclusion : ∃ x y : ℤ, (544 : ℤ) = (128 : ℤ) * x + (96 : ℤ) * y := by
  have hgcd : (Int.gcd (128 : ℤ) (96 : ℤ) : ℤ) = 32 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (128 : ℤ) (96 : ℤ) (544 : ℤ)).2
  simpa [hgcd] using v18_small_short_test_0048_divides

end AtomicClaimCertificates
