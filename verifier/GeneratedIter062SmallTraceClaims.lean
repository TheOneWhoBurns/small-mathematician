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

theorem dav5_test_0003_gcd : Nat.gcd 36 66 = 6 := by
  norm_num [Nat.gcd]

theorem dav5_test_0003_step_0 : (66 : ℤ) = 1 * 36 + 30 := by
  norm_num

theorem dav5_test_0003_step_1 : (36 : ℤ) = 1 * 30 + 6 := by
  norm_num

theorem dav5_test_0003_step_2 : (30 : ℤ) = 5 * 6 + 0 := by
  norm_num

theorem dav5_test_0003_divides : ¬ (6 : ℤ) ∣ (38 : ℤ) := by
  norm_num

theorem dav5_test_0003_conclusion : ¬ (∃ x y : ℤ, (38 : ℤ) = (36 : ℤ) * x + (66 : ℤ) * y) := by
  have hgcd : (Int.gcd (36 : ℤ) (66 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (36 : ℤ) (66 : ℤ) (38 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0003_divides hd

theorem dav5_test_0011_gcd : Nat.gcd 88 120 = 8 := by
  norm_num [Nat.gcd]

theorem dav5_test_0011_step_0 : (120 : ℤ) = 1 * 88 + 32 := by
  norm_num

theorem dav5_test_0011_step_1 : (88 : ℤ) = 2 * 32 + 24 := by
  norm_num

theorem dav5_test_0011_step_2 : (32 : ℤ) = 1 * 24 + 8 := by
  norm_num

theorem dav5_test_0011_step_3 : (24 : ℤ) = 3 * 8 + 0 := by
  norm_num

theorem dav5_test_0011_divides : ¬ (8 : ℤ) ∣ (54 : ℤ) := by
  norm_num

theorem dav5_test_0011_conclusion : ¬ (∃ x y : ℤ, (54 : ℤ) = (88 : ℤ) * x + (120 : ℤ) * y) := by
  have hgcd : (Int.gcd (88 : ℤ) (120 : ℤ) : ℤ) = 8 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (88 : ℤ) (120 : ℤ) (54 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0011_divides hd

theorem dav5_test_0013_gcd : Nat.gcd 170 130 = 10 := by
  norm_num [Nat.gcd]

theorem dav5_test_0013_step_0 : (170 : ℤ) = 1 * 130 + 40 := by
  norm_num

theorem dav5_test_0013_step_1 : (130 : ℤ) = 3 * 40 + 10 := by
  norm_num

theorem dav5_test_0013_step_2 : (40 : ℤ) = 4 * 10 + 0 := by
  norm_num

theorem dav5_test_0013_divides : ¬ (10 : ℤ) ∣ (33 : ℤ) := by
  norm_num

theorem dav5_test_0013_conclusion : ¬ (∃ x y : ℤ, (33 : ℤ) = (170 : ℤ) * x + (130 : ℤ) * y) := by
  have hgcd : (Int.gcd (170 : ℤ) (130 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (170 : ℤ) (130 : ℤ) (33 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0013_divides hd

theorem dav5_test_0018_gcd : Nat.gcd 126 45 = 9 := by
  norm_num [Nat.gcd]

theorem dav5_test_0018_step_0 : (126 : ℤ) = 2 * 45 + 36 := by
  norm_num

theorem dav5_test_0018_step_1 : (45 : ℤ) = 1 * 36 + 9 := by
  norm_num

theorem dav5_test_0018_step_2 : (36 : ℤ) = 4 * 9 + 0 := by
  norm_num

theorem dav5_test_0018_divides : (9 : ℤ) ∣ (-18 : ℤ) := by
  norm_num

theorem dav5_test_0018_conclusion : ∃ x y : ℤ, (-18 : ℤ) = (126 : ℤ) * x + (45 : ℤ) * y := by
  have hgcd : (Int.gcd (126 : ℤ) (45 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (126 : ℤ) (45 : ℤ) (-18 : ℤ)).2
  rw [hgcd]
  exact dav5_test_0018_divides

theorem dav5_test_0021_gcd : Nat.gcd 22 33 = 11 := by
  norm_num [Nat.gcd]

theorem dav5_test_0021_step_0 : (33 : ℤ) = 1 * 22 + 11 := by
  norm_num

theorem dav5_test_0021_step_1 : (22 : ℤ) = 2 * 11 + 0 := by
  norm_num

theorem dav5_test_0021_divides : ¬ (11 : ℤ) ∣ (-136 : ℤ) := by
  norm_num

theorem dav5_test_0021_conclusion : ¬ (∃ x y : ℤ, (-136 : ℤ) = (22 : ℤ) * x + (33 : ℤ) * y) := by
  have hgcd : (Int.gcd (22 : ℤ) (33 : ℤ) : ℤ) = 11 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (22 : ℤ) (33 : ℤ) (-136 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0021_divides hd

theorem dav5_test_0025_gcd : Nat.gcd 78 60 = 6 := by
  norm_num [Nat.gcd]

theorem dav5_test_0025_step_0 : (78 : ℤ) = 1 * 60 + 18 := by
  norm_num

theorem dav5_test_0025_step_1 : (60 : ℤ) = 3 * 18 + 6 := by
  norm_num

theorem dav5_test_0025_step_2 : (18 : ℤ) = 3 * 6 + 0 := by
  norm_num

theorem dav5_test_0025_divides : ¬ (6 : ℤ) ∣ (94 : ℤ) := by
  norm_num

theorem dav5_test_0025_conclusion : ¬ (∃ x y : ℤ, (94 : ℤ) = (78 : ℤ) * x + (60 : ℤ) * y) := by
  have hgcd : (Int.gcd (78 : ℤ) (60 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (78 : ℤ) (60 : ℤ) (94 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0025_divides hd

theorem dav5_test_0026_gcd : Nat.gcd 72 52 = 4 := by
  norm_num [Nat.gcd]

theorem dav5_test_0026_step_0 : (72 : ℤ) = 1 * 52 + 20 := by
  norm_num

theorem dav5_test_0026_step_1 : (52 : ℤ) = 2 * 20 + 12 := by
  norm_num

theorem dav5_test_0026_step_2 : (20 : ℤ) = 1 * 12 + 8 := by
  norm_num

theorem dav5_test_0026_step_3 : (12 : ℤ) = 1 * 8 + 4 := by
  norm_num

theorem dav5_test_0026_step_4 : (8 : ℤ) = 2 * 4 + 0 := by
  norm_num

theorem dav5_test_0026_divides : (4 : ℤ) ∣ (-20 : ℤ) := by
  norm_num

theorem dav5_test_0026_conclusion : ∃ x y : ℤ, (-20 : ℤ) = (72 : ℤ) * x + (52 : ℤ) * y := by
  have hgcd : (Int.gcd (72 : ℤ) (52 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (72 : ℤ) (52 : ℤ) (-20 : ℤ)).2
  rw [hgcd]
  exact dav5_test_0026_divides

theorem dav5_test_0027_gcd : Nat.gcd 130 120 = 10 := by
  norm_num [Nat.gcd]

theorem dav5_test_0027_step_0 : (130 : ℤ) = 1 * 120 + 10 := by
  norm_num

theorem dav5_test_0027_step_1 : (120 : ℤ) = 12 * 10 + 0 := by
  norm_num

theorem dav5_test_0027_divides : ¬ (10 : ℤ) ∣ (-105 : ℤ) := by
  norm_num

theorem dav5_test_0027_conclusion : ¬ (∃ x y : ℤ, (-105 : ℤ) = (130 : ℤ) * x + (120 : ℤ) * y) := by
  have hgcd : (Int.gcd (130 : ℤ) (120 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (130 : ℤ) (120 : ℤ) (-105 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0027_divides hd

theorem dav5_test_0031_gcd : Nat.gcd 98 63 = 7 := by
  norm_num [Nat.gcd]

theorem dav5_test_0031_step_0 : (98 : ℤ) = 1 * 63 + 35 := by
  norm_num

theorem dav5_test_0031_step_1 : (63 : ℤ) = 1 * 35 + 28 := by
  norm_num

theorem dav5_test_0031_step_2 : (35 : ℤ) = 1 * 28 + 7 := by
  norm_num

theorem dav5_test_0031_step_3 : (28 : ℤ) = 4 * 7 + 0 := by
  norm_num

theorem dav5_test_0031_divides : ¬ (7 : ℤ) ∣ (45 : ℤ) := by
  norm_num

theorem dav5_test_0031_conclusion : ¬ (∃ x y : ℤ, (45 : ℤ) = (98 : ℤ) * x + (63 : ℤ) * y) := by
  have hgcd : (Int.gcd (98 : ℤ) (63 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (98 : ℤ) (63 : ℤ) (45 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0031_divides hd

theorem dav5_test_0035_gcd : Nat.gcd 63 70 = 7 := by
  norm_num [Nat.gcd]

theorem dav5_test_0035_step_0 : (70 : ℤ) = 1 * 63 + 7 := by
  norm_num

theorem dav5_test_0035_step_1 : (63 : ℤ) = 9 * 7 + 0 := by
  norm_num

theorem dav5_test_0035_divides : ¬ (7 : ℤ) ∣ (-82 : ℤ) := by
  norm_num

theorem dav5_test_0035_conclusion : ¬ (∃ x y : ℤ, (-82 : ℤ) = (63 : ℤ) * x + (70 : ℤ) * y) := by
  have hgcd : (Int.gcd (63 : ℤ) (70 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (63 : ℤ) (70 : ℤ) (-82 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0035_divides hd

theorem dav5_test_0039_gcd : Nat.gcd 35 80 = 5 := by
  norm_num [Nat.gcd]

theorem dav5_test_0039_step_0 : (80 : ℤ) = 2 * 35 + 10 := by
  norm_num

theorem dav5_test_0039_step_1 : (35 : ℤ) = 3 * 10 + 5 := by
  norm_num

theorem dav5_test_0039_step_2 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem dav5_test_0039_divides : ¬ (5 : ℤ) ∣ (22 : ℤ) := by
  norm_num

theorem dav5_test_0039_conclusion : ¬ (∃ x y : ℤ, (22 : ℤ) = (35 : ℤ) * x + (80 : ℤ) * y) := by
  have hgcd : (Int.gcd (35 : ℤ) (80 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (35 : ℤ) (80 : ℤ) (22 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0039_divides hd

theorem dav5_test_0041_gcd : Nat.gcd 132 60 = 12 := by
  norm_num [Nat.gcd]

theorem dav5_test_0041_step_0 : (132 : ℤ) = 2 * 60 + 12 := by
  norm_num

theorem dav5_test_0041_step_1 : (60 : ℤ) = 5 * 12 + 0 := by
  norm_num

theorem dav5_test_0041_divides : ¬ (12 : ℤ) ∣ (175 : ℤ) := by
  norm_num

theorem dav5_test_0041_conclusion : ¬ (∃ x y : ℤ, (175 : ℤ) = (132 : ℤ) * x + (60 : ℤ) * y) := by
  have hgcd : (Int.gcd (132 : ℤ) (60 : ℤ) : ℤ) = 12 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (132 : ℤ) (60 : ℤ) (175 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0041_divides hd

theorem dav5_test_0042_gcd : Nat.gcd 80 50 = 10 := by
  norm_num [Nat.gcd]

theorem dav5_test_0042_step_0 : (80 : ℤ) = 1 * 50 + 30 := by
  norm_num

theorem dav5_test_0042_step_1 : (50 : ℤ) = 1 * 30 + 20 := by
  norm_num

theorem dav5_test_0042_step_2 : (30 : ℤ) = 1 * 20 + 10 := by
  norm_num

theorem dav5_test_0042_step_3 : (20 : ℤ) = 2 * 10 + 0 := by
  norm_num

theorem dav5_test_0042_divides : (10 : ℤ) ∣ (150 : ℤ) := by
  norm_num

theorem dav5_test_0042_conclusion : ∃ x y : ℤ, (150 : ℤ) = (80 : ℤ) * x + (50 : ℤ) * y := by
  have hgcd : (Int.gcd (80 : ℤ) (50 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (80 : ℤ) (50 : ℤ) (150 : ℤ)).2
  rw [hgcd]
  exact dav5_test_0042_divides

theorem dav5_test_0043_gcd : Nat.gcd 84 216 = 12 := by
  norm_num [Nat.gcd]

theorem dav5_test_0043_step_0 : (216 : ℤ) = 2 * 84 + 48 := by
  norm_num

theorem dav5_test_0043_step_1 : (84 : ℤ) = 1 * 48 + 36 := by
  norm_num

theorem dav5_test_0043_step_2 : (48 : ℤ) = 1 * 36 + 12 := by
  norm_num

theorem dav5_test_0043_step_3 : (36 : ℤ) = 3 * 12 + 0 := by
  norm_num

theorem dav5_test_0043_divides : ¬ (12 : ℤ) ∣ (76 : ℤ) := by
  norm_num

theorem dav5_test_0043_conclusion : ¬ (∃ x y : ℤ, (76 : ℤ) = (84 : ℤ) * x + (216 : ℤ) * y) := by
  have hgcd : (Int.gcd (84 : ℤ) (216 : ℤ) : ℤ) = 12 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (84 : ℤ) (216 : ℤ) (76 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0043_divides hd

theorem dav5_test_0045_gcd : Nat.gcd 63 144 = 9 := by
  norm_num [Nat.gcd]

theorem dav5_test_0045_step_0 : (144 : ℤ) = 2 * 63 + 18 := by
  norm_num

theorem dav5_test_0045_step_1 : (63 : ℤ) = 3 * 18 + 9 := by
  norm_num

theorem dav5_test_0045_step_2 : (18 : ℤ) = 2 * 9 + 0 := by
  norm_num

theorem dav5_test_0045_divides : ¬ (9 : ℤ) ∣ (-74 : ℤ) := by
  norm_num

theorem dav5_test_0045_conclusion : ¬ (∃ x y : ℤ, (-74 : ℤ) = (63 : ℤ) * x + (144 : ℤ) * y) := by
  have hgcd : (Int.gcd (63 : ℤ) (144 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (63 : ℤ) (144 : ℤ) (-74 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0045_divides hd

theorem dav5_test_0047_gcd : Nat.gcd 72 153 = 9 := by
  norm_num [Nat.gcd]

theorem dav5_test_0047_step_0 : (153 : ℤ) = 2 * 72 + 9 := by
  norm_num

theorem dav5_test_0047_step_1 : (72 : ℤ) = 8 * 9 + 0 := by
  norm_num

theorem dav5_test_0047_divides : ¬ (9 : ℤ) ∣ (105 : ℤ) := by
  norm_num

theorem dav5_test_0047_conclusion : ¬ (∃ x y : ℤ, (105 : ℤ) = (72 : ℤ) * x + (153 : ℤ) * y) := by
  have hgcd : (Int.gcd (72 : ℤ) (153 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (72 : ℤ) (153 : ℤ) (105 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0047_divides hd

theorem dav5_test_0053_gcd : Nat.gcd 90 80 = 10 := by
  norm_num [Nat.gcd]

theorem dav5_test_0053_step_0 : (90 : ℤ) = 1 * 80 + 10 := by
  norm_num

theorem dav5_test_0053_step_1 : (80 : ℤ) = 8 * 10 + 0 := by
  norm_num

theorem dav5_test_0053_divides : ¬ (10 : ℤ) ∣ (-121 : ℤ) := by
  norm_num

theorem dav5_test_0053_conclusion : ¬ (∃ x y : ℤ, (-121 : ℤ) = (90 : ℤ) * x + (80 : ℤ) * y) := by
  have hgcd : (Int.gcd (90 : ℤ) (80 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (90 : ℤ) (80 : ℤ) (-121 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0053_divides hd

theorem dav5_test_0054_gcd : Nat.gcd 26 14 = 2 := by
  norm_num [Nat.gcd]

theorem dav5_test_0054_step_0 : (26 : ℤ) = 1 * 14 + 12 := by
  norm_num

theorem dav5_test_0054_step_1 : (14 : ℤ) = 1 * 12 + 2 := by
  norm_num

theorem dav5_test_0054_step_2 : (12 : ℤ) = 6 * 2 + 0 := by
  norm_num

theorem dav5_test_0054_divides : (2 : ℤ) ∣ (-18 : ℤ) := by
  norm_num

theorem dav5_test_0054_conclusion : ∃ x y : ℤ, (-18 : ℤ) = (26 : ℤ) * x + (14 : ℤ) * y := by
  have hgcd : (Int.gcd (26 : ℤ) (14 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (26 : ℤ) (14 : ℤ) (-18 : ℤ)).2
  rw [hgcd]
  exact dav5_test_0054_divides

theorem dav5_test_0057_gcd : Nat.gcd 187 165 = 11 := by
  norm_num [Nat.gcd]

theorem dav5_test_0057_step_0 : (187 : ℤ) = 1 * 165 + 22 := by
  norm_num

theorem dav5_test_0057_step_1 : (165 : ℤ) = 7 * 22 + 11 := by
  norm_num

theorem dav5_test_0057_step_2 : (22 : ℤ) = 2 * 11 + 0 := by
  norm_num

theorem dav5_test_0057_divides : ¬ (11 : ℤ) ∣ (60 : ℤ) := by
  norm_num

theorem dav5_test_0057_conclusion : ¬ (∃ x y : ℤ, (60 : ℤ) = (187 : ℤ) * x + (165 : ℤ) * y) := by
  have hgcd : (Int.gcd (187 : ℤ) (165 : ℤ) : ℤ) = 11 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (187 : ℤ) (165 : ℤ) (60 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0057_divides hd

theorem dav5_test_0059_gcd : Nat.gcd 70 170 = 10 := by
  norm_num [Nat.gcd]

theorem dav5_test_0059_step_0 : (170 : ℤ) = 2 * 70 + 30 := by
  norm_num

theorem dav5_test_0059_step_1 : (70 : ℤ) = 2 * 30 + 10 := by
  norm_num

theorem dav5_test_0059_step_2 : (30 : ℤ) = 3 * 10 + 0 := by
  norm_num

theorem dav5_test_0059_divides : ¬ (10 : ℤ) ∣ (28 : ℤ) := by
  norm_num

theorem dav5_test_0059_conclusion : ¬ (∃ x y : ℤ, (28 : ℤ) = (70 : ℤ) * x + (170 : ℤ) * y) := by
  have hgcd : (Int.gcd (70 : ℤ) (170 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (70 : ℤ) (170 : ℤ) (28 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0059_divides hd

theorem dav5_test_0065_gcd : Nat.gcd 77 28 = 7 := by
  norm_num [Nat.gcd]

theorem dav5_test_0065_step_0 : (77 : ℤ) = 2 * 28 + 21 := by
  norm_num

theorem dav5_test_0065_step_1 : (28 : ℤ) = 1 * 21 + 7 := by
  norm_num

theorem dav5_test_0065_step_2 : (21 : ℤ) = 3 * 7 + 0 := by
  norm_num

theorem dav5_test_0065_divides : ¬ (7 : ℤ) ∣ (-6 : ℤ) := by
  norm_num

theorem dav5_test_0065_conclusion : ¬ (∃ x y : ℤ, (-6 : ℤ) = (77 : ℤ) * x + (28 : ℤ) * y) := by
  have hgcd : (Int.gcd (77 : ℤ) (28 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (77 : ℤ) (28 : ℤ) (-6 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0065_divides hd

theorem dav5_test_0066_gcd : Nat.gcd 108 66 = 6 := by
  norm_num [Nat.gcd]

theorem dav5_test_0066_step_0 : (108 : ℤ) = 1 * 66 + 42 := by
  norm_num

theorem dav5_test_0066_step_1 : (66 : ℤ) = 1 * 42 + 24 := by
  norm_num

theorem dav5_test_0066_step_2 : (42 : ℤ) = 1 * 24 + 18 := by
  norm_num

theorem dav5_test_0066_step_3 : (24 : ℤ) = 1 * 18 + 6 := by
  norm_num

theorem dav5_test_0066_step_4 : (18 : ℤ) = 3 * 6 + 0 := by
  norm_num

theorem dav5_test_0066_divides : (6 : ℤ) ∣ (-90 : ℤ) := by
  norm_num

theorem dav5_test_0066_conclusion : ∃ x y : ℤ, (-90 : ℤ) = (108 : ℤ) * x + (66 : ℤ) * y := by
  have hgcd : (Int.gcd (108 : ℤ) (66 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (108 : ℤ) (66 : ℤ) (-90 : ℤ)).2
  rw [hgcd]
  exact dav5_test_0066_divides

theorem dav5_test_0070_gcd : Nat.gcd 144 104 = 8 := by
  norm_num [Nat.gcd]

theorem dav5_test_0070_step_0 : (144 : ℤ) = 1 * 104 + 40 := by
  norm_num

theorem dav5_test_0070_step_1 : (104 : ℤ) = 2 * 40 + 24 := by
  norm_num

theorem dav5_test_0070_step_2 : (40 : ℤ) = 1 * 24 + 16 := by
  norm_num

theorem dav5_test_0070_step_3 : (24 : ℤ) = 1 * 16 + 8 := by
  norm_num

theorem dav5_test_0070_step_4 : (16 : ℤ) = 2 * 8 + 0 := by
  norm_num

theorem dav5_test_0070_divides : (8 : ℤ) ∣ (-8 : ℤ) := by
  norm_num

theorem dav5_test_0070_conclusion : ∃ x y : ℤ, (-8 : ℤ) = (144 : ℤ) * x + (104 : ℤ) * y := by
  have hgcd : (Int.gcd (144 : ℤ) (104 : ℤ) : ℤ) = 8 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (144 : ℤ) (104 : ℤ) (-8 : ℤ)).2
  rw [hgcd]
  exact dav5_test_0070_divides

theorem dav5_test_0071_gcd : Nat.gcd 168 204 = 12 := by
  norm_num [Nat.gcd]

theorem dav5_test_0071_step_0 : (204 : ℤ) = 1 * 168 + 36 := by
  norm_num

theorem dav5_test_0071_step_1 : (168 : ℤ) = 4 * 36 + 24 := by
  norm_num

theorem dav5_test_0071_step_2 : (36 : ℤ) = 1 * 24 + 12 := by
  norm_num

theorem dav5_test_0071_step_3 : (24 : ℤ) = 2 * 12 + 0 := by
  norm_num

theorem dav5_test_0071_divides : ¬ (12 : ℤ) ∣ (149 : ℤ) := by
  norm_num

theorem dav5_test_0071_conclusion : ¬ (∃ x y : ℤ, (149 : ℤ) = (168 : ℤ) * x + (204 : ℤ) * y) := by
  have hgcd : (Int.gcd (168 : ℤ) (204 : ℤ) : ℤ) = 12 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (168 : ℤ) (204 : ℤ) (149 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0071_divides hd

theorem dav5_test_0073_gcd : Nat.gcd 66 72 = 6 := by
  norm_num [Nat.gcd]

theorem dav5_test_0073_step_0 : (72 : ℤ) = 1 * 66 + 6 := by
  norm_num

theorem dav5_test_0073_step_1 : (66 : ℤ) = 11 * 6 + 0 := by
  norm_num

theorem dav5_test_0073_divides : ¬ (6 : ℤ) ∣ (-53 : ℤ) := by
  norm_num

theorem dav5_test_0073_conclusion : ¬ (∃ x y : ℤ, (-53 : ℤ) = (66 : ℤ) * x + (72 : ℤ) * y) := by
  have hgcd : (Int.gcd (66 : ℤ) (72 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (66 : ℤ) (72 : ℤ) (-53 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0073_divides hd

theorem dav5_test_0079_gcd : Nat.gcd 54 63 = 9 := by
  norm_num [Nat.gcd]

theorem dav5_test_0079_step_0 : (63 : ℤ) = 1 * 54 + 9 := by
  norm_num

theorem dav5_test_0079_step_1 : (54 : ℤ) = 6 * 9 + 0 := by
  norm_num

theorem dav5_test_0079_divides : ¬ (9 : ℤ) ∣ (-70 : ℤ) := by
  norm_num

theorem dav5_test_0079_conclusion : ¬ (∃ x y : ℤ, (-70 : ℤ) = (54 : ℤ) * x + (63 : ℤ) * y) := by
  have hgcd : (Int.gcd (54 : ℤ) (63 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (54 : ℤ) (63 : ℤ) (-70 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0079_divides hd

theorem dav5_test_0081_gcd : Nat.gcd 64 72 = 8 := by
  norm_num [Nat.gcd]

theorem dav5_test_0081_step_0 : (72 : ℤ) = 1 * 64 + 8 := by
  norm_num

theorem dav5_test_0081_step_1 : (64 : ℤ) = 8 * 8 + 0 := by
  norm_num

theorem dav5_test_0081_divides : ¬ (8 : ℤ) ∣ (-6 : ℤ) := by
  norm_num

theorem dav5_test_0081_conclusion : ¬ (∃ x y : ℤ, (-6 : ℤ) = (64 : ℤ) * x + (72 : ℤ) * y) := by
  have hgcd : (Int.gcd (64 : ℤ) (72 : ℤ) : ℤ) = 8 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (64 : ℤ) (72 : ℤ) (-6 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0081_divides hd

theorem dav5_test_0090_gcd : Nat.gcd 14 20 = 2 := by
  norm_num [Nat.gcd]

theorem dav5_test_0090_step_0 : (20 : ℤ) = 1 * 14 + 6 := by
  norm_num

theorem dav5_test_0090_step_1 : (14 : ℤ) = 2 * 6 + 2 := by
  norm_num

theorem dav5_test_0090_step_2 : (6 : ℤ) = 3 * 2 + 0 := by
  norm_num

theorem dav5_test_0090_divides : (2 : ℤ) ∣ (-2 : ℤ) := by
  norm_num

theorem dav5_test_0090_conclusion : ∃ x y : ℤ, (-2 : ℤ) = (14 : ℤ) * x + (20 : ℤ) * y := by
  have hgcd : (Int.gcd (14 : ℤ) (20 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (14 : ℤ) (20 : ℤ) (-2 : ℤ)).2
  rw [hgcd]
  exact dav5_test_0090_divides

theorem dav5_test_0093_gcd : Nat.gcd 132 204 = 12 := by
  norm_num [Nat.gcd]

theorem dav5_test_0093_step_0 : (204 : ℤ) = 1 * 132 + 72 := by
  norm_num

theorem dav5_test_0093_step_1 : (132 : ℤ) = 1 * 72 + 60 := by
  norm_num

theorem dav5_test_0093_step_2 : (72 : ℤ) = 1 * 60 + 12 := by
  norm_num

theorem dav5_test_0093_step_3 : (60 : ℤ) = 5 * 12 + 0 := by
  norm_num

theorem dav5_test_0093_divides : ¬ (12 : ℤ) ∣ (102 : ℤ) := by
  norm_num

theorem dav5_test_0093_conclusion : ¬ (∃ x y : ℤ, (102 : ℤ) = (132 : ℤ) * x + (204 : ℤ) * y) := by
  have hgcd : (Int.gcd (132 : ℤ) (204 : ℤ) : ℤ) = 12 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (132 : ℤ) (204 : ℤ) (102 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0093_divides hd

theorem dav5_test_0096_gcd : Nat.gcd 72 132 = 12 := by
  norm_num [Nat.gcd]

theorem dav5_test_0096_step_0 : (132 : ℤ) = 1 * 72 + 60 := by
  norm_num

theorem dav5_test_0096_step_1 : (72 : ℤ) = 1 * 60 + 12 := by
  norm_num

theorem dav5_test_0096_step_2 : (60 : ℤ) = 5 * 12 + 0 := by
  norm_num

theorem dav5_test_0096_divides : (12 : ℤ) ∣ (120 : ℤ) := by
  norm_num

theorem dav5_test_0096_conclusion : ∃ x y : ℤ, (120 : ℤ) = (72 : ℤ) * x + (132 : ℤ) * y := by
  have hgcd : (Int.gcd (72 : ℤ) (132 : ℤ) : ℤ) = 12 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (72 : ℤ) (132 : ℤ) (120 : ℤ)).2
  rw [hgcd]
  exact dav5_test_0096_divides

theorem dav5_test_0098_gcd : Nat.gcd 54 15 = 3 := by
  norm_num [Nat.gcd]

theorem dav5_test_0098_step_0 : (54 : ℤ) = 3 * 15 + 9 := by
  norm_num

theorem dav5_test_0098_step_1 : (15 : ℤ) = 1 * 9 + 6 := by
  norm_num

theorem dav5_test_0098_step_2 : (9 : ℤ) = 1 * 6 + 3 := by
  norm_num

theorem dav5_test_0098_step_3 : (6 : ℤ) = 2 * 3 + 0 := by
  norm_num

theorem dav5_test_0098_divides : (3 : ℤ) ∣ (30 : ℤ) := by
  norm_num

theorem dav5_test_0098_conclusion : ∃ x y : ℤ, (30 : ℤ) = (54 : ℤ) * x + (15 : ℤ) * y := by
  have hgcd : (Int.gcd (54 : ℤ) (15 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (54 : ℤ) (15 : ℤ) (30 : ℤ)).2
  rw [hgcd]
  exact dav5_test_0098_divides

theorem dav5_test_0099_gcd : Nat.gcd 60 64 = 4 := by
  norm_num [Nat.gcd]

theorem dav5_test_0099_step_0 : (64 : ℤ) = 1 * 60 + 4 := by
  norm_num

theorem dav5_test_0099_step_1 : (60 : ℤ) = 15 * 4 + 0 := by
  norm_num

theorem dav5_test_0099_divides : ¬ (4 : ℤ) ∣ (-42 : ℤ) := by
  norm_num

theorem dav5_test_0099_conclusion : ¬ (∃ x y : ℤ, (-42 : ℤ) = (60 : ℤ) * x + (64 : ℤ) * y) := by
  have hgcd : (Int.gcd (60 : ℤ) (64 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (60 : ℤ) (64 : ℤ) (-42 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0099_divides hd

theorem dav5_test_0102_gcd : Nat.gcd 110 180 = 10 := by
  norm_num [Nat.gcd]

theorem dav5_test_0102_step_0 : (180 : ℤ) = 1 * 110 + 70 := by
  norm_num

theorem dav5_test_0102_step_1 : (110 : ℤ) = 1 * 70 + 40 := by
  norm_num

theorem dav5_test_0102_step_2 : (70 : ℤ) = 1 * 40 + 30 := by
  norm_num

theorem dav5_test_0102_step_3 : (40 : ℤ) = 1 * 30 + 10 := by
  norm_num

theorem dav5_test_0102_step_4 : (30 : ℤ) = 3 * 10 + 0 := by
  norm_num

theorem dav5_test_0102_divides : (10 : ℤ) ∣ (130 : ℤ) := by
  norm_num

theorem dav5_test_0102_conclusion : ∃ x y : ℤ, (130 : ℤ) = (110 : ℤ) * x + (180 : ℤ) * y := by
  have hgcd : (Int.gcd (110 : ℤ) (180 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (110 : ℤ) (180 : ℤ) (130 : ℤ)).2
  rw [hgcd]
  exact dav5_test_0102_divides

theorem dav5_test_0107_gcd : Nat.gcd 60 54 = 6 := by
  norm_num [Nat.gcd]

theorem dav5_test_0107_step_0 : (60 : ℤ) = 1 * 54 + 6 := by
  norm_num

theorem dav5_test_0107_step_1 : (54 : ℤ) = 9 * 6 + 0 := by
  norm_num

theorem dav5_test_0107_divides : ¬ (6 : ℤ) ∣ (65 : ℤ) := by
  norm_num

theorem dav5_test_0107_conclusion : ¬ (∃ x y : ℤ, (65 : ℤ) = (60 : ℤ) * x + (54 : ℤ) * y) := by
  have hgcd : (Int.gcd (60 : ℤ) (54 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (60 : ℤ) (54 : ℤ) (65 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0107_divides hd

theorem dav5_test_0109_gcd : Nat.gcd 112 21 = 7 := by
  norm_num [Nat.gcd]

theorem dav5_test_0109_step_0 : (112 : ℤ) = 5 * 21 + 7 := by
  norm_num

theorem dav5_test_0109_step_1 : (21 : ℤ) = 3 * 7 + 0 := by
  norm_num

theorem dav5_test_0109_divides : ¬ (7 : ℤ) ∣ (-29 : ℤ) := by
  norm_num

theorem dav5_test_0109_conclusion : ¬ (∃ x y : ℤ, (-29 : ℤ) = (112 : ℤ) * x + (21 : ℤ) * y) := by
  have hgcd : (Int.gcd (112 : ℤ) (21 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (112 : ℤ) (21 : ℤ) (-29 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0109_divides hd

theorem dav5_test_0114_gcd : Nat.gcd 22 14 = 2 := by
  norm_num [Nat.gcd]

theorem dav5_test_0114_step_0 : (22 : ℤ) = 1 * 14 + 8 := by
  norm_num

theorem dav5_test_0114_step_1 : (14 : ℤ) = 1 * 8 + 6 := by
  norm_num

theorem dav5_test_0114_step_2 : (8 : ℤ) = 1 * 6 + 2 := by
  norm_num

theorem dav5_test_0114_step_3 : (6 : ℤ) = 3 * 2 + 0 := by
  norm_num

theorem dav5_test_0114_divides : (2 : ℤ) ∣ (10 : ℤ) := by
  norm_num

theorem dav5_test_0114_conclusion : ∃ x y : ℤ, (10 : ℤ) = (22 : ℤ) * x + (14 : ℤ) * y := by
  have hgcd : (Int.gcd (22 : ℤ) (14 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (22 : ℤ) (14 : ℤ) (10 : ℤ)).2
  rw [hgcd]
  exact dav5_test_0114_divides

theorem dav5_test_0118_gcd : Nat.gcd 162 45 = 9 := by
  norm_num [Nat.gcd]

theorem dav5_test_0118_step_0 : (162 : ℤ) = 3 * 45 + 27 := by
  norm_num

theorem dav5_test_0118_step_1 : (45 : ℤ) = 1 * 27 + 18 := by
  norm_num

theorem dav5_test_0118_step_2 : (27 : ℤ) = 1 * 18 + 9 := by
  norm_num

theorem dav5_test_0118_step_3 : (18 : ℤ) = 2 * 9 + 0 := by
  norm_num

theorem dav5_test_0118_divides : (9 : ℤ) ∣ (-36 : ℤ) := by
  norm_num

theorem dav5_test_0118_conclusion : ∃ x y : ℤ, (-36 : ℤ) = (162 : ℤ) * x + (45 : ℤ) * y := by
  have hgcd : (Int.gcd (162 : ℤ) (45 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (162 : ℤ) (45 : ℤ) (-36 : ℤ)).2
  rw [hgcd]
  exact dav5_test_0118_divides

theorem dav5_test_0123_gcd : Nat.gcd 120 130 = 10 := by
  norm_num [Nat.gcd]

theorem dav5_test_0123_step_0 : (130 : ℤ) = 1 * 120 + 10 := by
  norm_num

theorem dav5_test_0123_step_1 : (120 : ℤ) = 12 * 10 + 0 := by
  norm_num

theorem dav5_test_0123_divides : ¬ (10 : ℤ) ∣ (94 : ℤ) := by
  norm_num

theorem dav5_test_0123_conclusion : ¬ (∃ x y : ℤ, (94 : ℤ) = (120 : ℤ) * x + (130 : ℤ) * y) := by
  have hgcd : (Int.gcd (120 : ℤ) (130 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (120 : ℤ) (130 : ℤ) (94 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0123_divides hd

theorem dav5_test_0126_gcd : Nat.gcd 14 22 = 2 := by
  norm_num [Nat.gcd]

theorem dav5_test_0126_step_0 : (22 : ℤ) = 1 * 14 + 8 := by
  norm_num

theorem dav5_test_0126_step_1 : (14 : ℤ) = 1 * 8 + 6 := by
  norm_num

theorem dav5_test_0126_step_2 : (8 : ℤ) = 1 * 6 + 2 := by
  norm_num

theorem dav5_test_0126_step_3 : (6 : ℤ) = 3 * 2 + 0 := by
  norm_num

theorem dav5_test_0126_divides : (2 : ℤ) ∣ (18 : ℤ) := by
  norm_num

theorem dav5_test_0126_conclusion : ∃ x y : ℤ, (18 : ℤ) = (14 : ℤ) * x + (22 : ℤ) * y := by
  have hgcd : (Int.gcd (14 : ℤ) (22 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (14 : ℤ) (22 : ℤ) (18 : ℤ)).2
  rw [hgcd]
  exact dav5_test_0126_divides

theorem dav5_test_0129_gcd : Nat.gcd 14 21 = 7 := by
  norm_num [Nat.gcd]

theorem dav5_test_0129_step_0 : (21 : ℤ) = 1 * 14 + 7 := by
  norm_num

theorem dav5_test_0129_step_1 : (14 : ℤ) = 2 * 7 + 0 := by
  norm_num

theorem dav5_test_0129_divides : ¬ (7 : ℤ) ∣ (-82 : ℤ) := by
  norm_num

theorem dav5_test_0129_conclusion : ¬ (∃ x y : ℤ, (-82 : ℤ) = (14 : ℤ) * x + (21 : ℤ) * y) := by
  have hgcd : (Int.gcd (14 : ℤ) (21 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (14 : ℤ) (21 : ℤ) (-82 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0129_divides hd

theorem dav5_test_0130_gcd : Nat.gcd 85 45 = 5 := by
  norm_num [Nat.gcd]

theorem dav5_test_0130_step_0 : (85 : ℤ) = 1 * 45 + 40 := by
  norm_num

theorem dav5_test_0130_step_1 : (45 : ℤ) = 1 * 40 + 5 := by
  norm_num

theorem dav5_test_0130_step_2 : (40 : ℤ) = 8 * 5 + 0 := by
  norm_num

theorem dav5_test_0130_divides : (5 : ℤ) ∣ (-70 : ℤ) := by
  norm_num

theorem dav5_test_0130_conclusion : ∃ x y : ℤ, (-70 : ℤ) = (85 : ℤ) * x + (45 : ℤ) * y := by
  have hgcd : (Int.gcd (85 : ℤ) (45 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (85 : ℤ) (45 : ℤ) (-70 : ℤ)).2
  rw [hgcd]
  exact dav5_test_0130_divides

theorem dav5_test_0131_gcd : Nat.gcd 54 63 = 9 := by
  norm_num [Nat.gcd]

theorem dav5_test_0131_step_0 : (63 : ℤ) = 1 * 54 + 9 := by
  norm_num

theorem dav5_test_0131_step_1 : (54 : ℤ) = 6 * 9 + 0 := by
  norm_num

theorem dav5_test_0131_divides : ¬ (9 : ℤ) ∣ (56 : ℤ) := by
  norm_num

theorem dav5_test_0131_conclusion : ¬ (∃ x y : ℤ, (56 : ℤ) = (54 : ℤ) * x + (63 : ℤ) * y) := by
  have hgcd : (Int.gcd (54 : ℤ) (63 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (54 : ℤ) (63 : ℤ) (56 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0131_divides hd

theorem dav5_test_0133_gcd : Nat.gcd 70 55 = 5 := by
  norm_num [Nat.gcd]

theorem dav5_test_0133_step_0 : (70 : ℤ) = 1 * 55 + 15 := by
  norm_num

theorem dav5_test_0133_step_1 : (55 : ℤ) = 3 * 15 + 10 := by
  norm_num

theorem dav5_test_0133_step_2 : (15 : ℤ) = 1 * 10 + 5 := by
  norm_num

theorem dav5_test_0133_step_3 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem dav5_test_0133_divides : ¬ (5 : ℤ) ∣ (-39 : ℤ) := by
  norm_num

theorem dav5_test_0133_conclusion : ¬ (∃ x y : ℤ, (-39 : ℤ) = (70 : ℤ) * x + (55 : ℤ) * y) := by
  have hgcd : (Int.gcd (70 : ℤ) (55 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (70 : ℤ) (55 : ℤ) (-39 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0133_divides hd

theorem dav5_test_0139_gcd : Nat.gcd 187 88 = 11 := by
  norm_num [Nat.gcd]

theorem dav5_test_0139_step_0 : (187 : ℤ) = 2 * 88 + 11 := by
  norm_num

theorem dav5_test_0139_step_1 : (88 : ℤ) = 8 * 11 + 0 := by
  norm_num

theorem dav5_test_0139_divides : ¬ (11 : ℤ) ∣ (-81 : ℤ) := by
  norm_num

theorem dav5_test_0139_conclusion : ¬ (∃ x y : ℤ, (-81 : ℤ) = (187 : ℤ) * x + (88 : ℤ) * y) := by
  have hgcd : (Int.gcd (187 : ℤ) (88 : ℤ) : ℤ) = 11 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (187 : ℤ) (88 : ℤ) (-81 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0139_divides hd

theorem dav5_test_0141_gcd : Nat.gcd 6 9 = 3 := by
  norm_num [Nat.gcd]

theorem dav5_test_0141_step_0 : (9 : ℤ) = 1 * 6 + 3 := by
  norm_num

theorem dav5_test_0141_step_1 : (6 : ℤ) = 2 * 3 + 0 := by
  norm_num

theorem dav5_test_0141_divides : ¬ (3 : ℤ) ∣ (34 : ℤ) := by
  norm_num

theorem dav5_test_0141_conclusion : ¬ (∃ x y : ℤ, (34 : ℤ) = (6 : ℤ) * x + (9 : ℤ) * y) := by
  have hgcd : (Int.gcd (6 : ℤ) (9 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (6 : ℤ) (9 : ℤ) (34 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0141_divides hd

theorem dav5_test_0143_gcd : Nat.gcd 6 8 = 2 := by
  norm_num [Nat.gcd]

theorem dav5_test_0143_step_0 : (8 : ℤ) = 1 * 6 + 2 := by
  norm_num

theorem dav5_test_0143_step_1 : (6 : ℤ) = 3 * 2 + 0 := by
  norm_num

theorem dav5_test_0143_divides : ¬ (2 : ℤ) ∣ (-11 : ℤ) := by
  norm_num

theorem dav5_test_0143_conclusion : ¬ (∃ x y : ℤ, (-11 : ℤ) = (6 : ℤ) * x + (8 : ℤ) * y) := by
  have hgcd : (Int.gcd (6 : ℤ) (8 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (6 : ℤ) (8 : ℤ) (-11 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0143_divides hd

theorem dav5_test_0145_gcd : Nat.gcd 84 66 = 6 := by
  norm_num [Nat.gcd]

theorem dav5_test_0145_step_0 : (84 : ℤ) = 1 * 66 + 18 := by
  norm_num

theorem dav5_test_0145_step_1 : (66 : ℤ) = 3 * 18 + 12 := by
  norm_num

theorem dav5_test_0145_step_2 : (18 : ℤ) = 1 * 12 + 6 := by
  norm_num

theorem dav5_test_0145_step_3 : (12 : ℤ) = 2 * 6 + 0 := by
  norm_num

theorem dav5_test_0145_divides : ¬ (6 : ℤ) ∣ (-10 : ℤ) := by
  norm_num

theorem dav5_test_0145_conclusion : ¬ (∃ x y : ℤ, (-10 : ℤ) = (84 : ℤ) * x + (66 : ℤ) * y) := by
  have hgcd : (Int.gcd (84 : ℤ) (66 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (84 : ℤ) (66 : ℤ) (-10 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0145_divides hd

theorem dav5_test_0146_gcd : Nat.gcd 24 10 = 2 := by
  norm_num [Nat.gcd]

theorem dav5_test_0146_step_0 : (24 : ℤ) = 2 * 10 + 4 := by
  norm_num

theorem dav5_test_0146_step_1 : (10 : ℤ) = 2 * 4 + 2 := by
  norm_num

theorem dav5_test_0146_step_2 : (4 : ℤ) = 2 * 2 + 0 := by
  norm_num

theorem dav5_test_0146_divides : (2 : ℤ) ∣ (28 : ℤ) := by
  norm_num

theorem dav5_test_0146_conclusion : ∃ x y : ℤ, (28 : ℤ) = (24 : ℤ) * x + (10 : ℤ) * y := by
  have hgcd : (Int.gcd (24 : ℤ) (10 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (24 : ℤ) (10 : ℤ) (28 : ℤ)).2
  rw [hgcd]
  exact dav5_test_0146_divides

theorem dav5_test_0149_gcd : Nat.gcd 28 36 = 4 := by
  norm_num [Nat.gcd]

theorem dav5_test_0149_step_0 : (36 : ℤ) = 1 * 28 + 8 := by
  norm_num

theorem dav5_test_0149_step_1 : (28 : ℤ) = 3 * 8 + 4 := by
  norm_num

theorem dav5_test_0149_step_2 : (8 : ℤ) = 2 * 4 + 0 := by
  norm_num

theorem dav5_test_0149_divides : ¬ (4 : ℤ) ∣ (-22 : ℤ) := by
  norm_num

theorem dav5_test_0149_conclusion : ¬ (∃ x y : ℤ, (-22 : ℤ) = (28 : ℤ) * x + (36 : ℤ) * y) := by
  have hgcd : (Int.gcd (28 : ℤ) (36 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (28 : ℤ) (36 : ℤ) (-22 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0149_divides hd

theorem dav5_test_0151_gcd : Nat.gcd 21 15 = 3 := by
  norm_num [Nat.gcd]

theorem dav5_test_0151_step_0 : (21 : ℤ) = 1 * 15 + 6 := by
  norm_num

theorem dav5_test_0151_step_1 : (15 : ℤ) = 2 * 6 + 3 := by
  norm_num

theorem dav5_test_0151_step_2 : (6 : ℤ) = 2 * 3 + 0 := by
  norm_num

theorem dav5_test_0151_divides : ¬ (3 : ℤ) ∣ (22 : ℤ) := by
  norm_num

theorem dav5_test_0151_conclusion : ¬ (∃ x y : ℤ, (22 : ℤ) = (21 : ℤ) * x + (15 : ℤ) * y) := by
  have hgcd : (Int.gcd (21 : ℤ) (15 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (21 : ℤ) (15 : ℤ) (22 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0151_divides hd

theorem dav5_test_0156_gcd : Nat.gcd 110 180 = 10 := by
  norm_num [Nat.gcd]

theorem dav5_test_0156_step_0 : (180 : ℤ) = 1 * 110 + 70 := by
  norm_num

theorem dav5_test_0156_step_1 : (110 : ℤ) = 1 * 70 + 40 := by
  norm_num

theorem dav5_test_0156_step_2 : (70 : ℤ) = 1 * 40 + 30 := by
  norm_num

theorem dav5_test_0156_step_3 : (40 : ℤ) = 1 * 30 + 10 := by
  norm_num

theorem dav5_test_0156_step_4 : (30 : ℤ) = 3 * 10 + 0 := by
  norm_num

theorem dav5_test_0156_divides : (10 : ℤ) ∣ (100 : ℤ) := by
  norm_num

theorem dav5_test_0156_conclusion : ∃ x y : ℤ, (100 : ℤ) = (110 : ℤ) * x + (180 : ℤ) * y := by
  have hgcd : (Int.gcd (110 : ℤ) (180 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (110 : ℤ) (180 : ℤ) (100 : ℤ)).2
  rw [hgcd]
  exact dav5_test_0156_divides

theorem dav5_test_0157_gcd : Nat.gcd 66 121 = 11 := by
  norm_num [Nat.gcd]

theorem dav5_test_0157_step_0 : (121 : ℤ) = 1 * 66 + 55 := by
  norm_num

theorem dav5_test_0157_step_1 : (66 : ℤ) = 1 * 55 + 11 := by
  norm_num

theorem dav5_test_0157_step_2 : (55 : ℤ) = 5 * 11 + 0 := by
  norm_num

theorem dav5_test_0157_divides : ¬ (11 : ℤ) ∣ (-125 : ℤ) := by
  norm_num

theorem dav5_test_0157_conclusion : ¬ (∃ x y : ℤ, (-125 : ℤ) = (66 : ℤ) * x + (121 : ℤ) * y) := by
  have hgcd : (Int.gcd (66 : ℤ) (121 : ℤ) : ℤ) = 11 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (66 : ℤ) (121 : ℤ) (-125 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0157_divides hd

theorem dav5_test_0161_gcd : Nat.gcd 72 52 = 4 := by
  norm_num [Nat.gcd]

theorem dav5_test_0161_step_0 : (72 : ℤ) = 1 * 52 + 20 := by
  norm_num

theorem dav5_test_0161_step_1 : (52 : ℤ) = 2 * 20 + 12 := by
  norm_num

theorem dav5_test_0161_step_2 : (20 : ℤ) = 1 * 12 + 8 := by
  norm_num

theorem dav5_test_0161_step_3 : (12 : ℤ) = 1 * 8 + 4 := by
  norm_num

theorem dav5_test_0161_step_4 : (8 : ℤ) = 2 * 4 + 0 := by
  norm_num

theorem dav5_test_0161_divides : ¬ (4 : ℤ) ∣ (59 : ℤ) := by
  norm_num

theorem dav5_test_0161_conclusion : ¬ (∃ x y : ℤ, (59 : ℤ) = (72 : ℤ) * x + (52 : ℤ) * y) := by
  have hgcd : (Int.gcd (72 : ℤ) (52 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (72 : ℤ) (52 : ℤ) (59 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0161_divides hd

theorem dav5_test_0162_gcd : Nat.gcd 136 104 = 8 := by
  norm_num [Nat.gcd]

theorem dav5_test_0162_step_0 : (136 : ℤ) = 1 * 104 + 32 := by
  norm_num

theorem dav5_test_0162_step_1 : (104 : ℤ) = 3 * 32 + 8 := by
  norm_num

theorem dav5_test_0162_step_2 : (32 : ℤ) = 4 * 8 + 0 := by
  norm_num

theorem dav5_test_0162_divides : (8 : ℤ) ∣ (-64 : ℤ) := by
  norm_num

theorem dav5_test_0162_conclusion : ∃ x y : ℤ, (-64 : ℤ) = (136 : ℤ) * x + (104 : ℤ) * y := by
  have hgcd : (Int.gcd (136 : ℤ) (104 : ℤ) : ℤ) = 8 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (136 : ℤ) (104 : ℤ) (-64 : ℤ)).2
  rw [hgcd]
  exact dav5_test_0162_divides

theorem dav5_test_0163_gcd : Nat.gcd 54 51 = 3 := by
  norm_num [Nat.gcd]

theorem dav5_test_0163_step_0 : (54 : ℤ) = 1 * 51 + 3 := by
  norm_num

theorem dav5_test_0163_step_1 : (51 : ℤ) = 17 * 3 + 0 := by
  norm_num

theorem dav5_test_0163_divides : ¬ (3 : ℤ) ∣ (-41 : ℤ) := by
  norm_num

theorem dav5_test_0163_conclusion : ¬ (∃ x y : ℤ, (-41 : ℤ) = (54 : ℤ) * x + (51 : ℤ) * y) := by
  have hgcd : (Int.gcd (54 : ℤ) (51 : ℤ) : ℤ) = 3 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (54 : ℤ) (51 : ℤ) (-41 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0163_divides hd

theorem dav5_test_0165_gcd : Nat.gcd 10 14 = 2 := by
  norm_num [Nat.gcd]

theorem dav5_test_0165_step_0 : (14 : ℤ) = 1 * 10 + 4 := by
  norm_num

theorem dav5_test_0165_step_1 : (10 : ℤ) = 2 * 4 + 2 := by
  norm_num

theorem dav5_test_0165_step_2 : (4 : ℤ) = 2 * 2 + 0 := by
  norm_num

theorem dav5_test_0165_divides : ¬ (2 : ℤ) ∣ (-7 : ℤ) := by
  norm_num

theorem dav5_test_0165_conclusion : ¬ (∃ x y : ℤ, (-7 : ℤ) = (10 : ℤ) * x + (14 : ℤ) * y) := by
  have hgcd : (Int.gcd (10 : ℤ) (14 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (10 : ℤ) (14 : ℤ) (-7 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0165_divides hd

theorem dav5_test_0175_gcd : Nat.gcd 36 66 = 6 := by
  norm_num [Nat.gcd]

theorem dav5_test_0175_step_0 : (66 : ℤ) = 1 * 36 + 30 := by
  norm_num

theorem dav5_test_0175_step_1 : (36 : ℤ) = 1 * 30 + 6 := by
  norm_num

theorem dav5_test_0175_step_2 : (30 : ℤ) = 5 * 6 + 0 := by
  norm_num

theorem dav5_test_0175_divides : ¬ (6 : ℤ) ∣ (52 : ℤ) := by
  norm_num

theorem dav5_test_0175_conclusion : ¬ (∃ x y : ℤ, (52 : ℤ) = (36 : ℤ) * x + (66 : ℤ) * y) := by
  have hgcd : (Int.gcd (36 : ℤ) (66 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (36 : ℤ) (66 : ℤ) (52 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0175_divides hd

theorem dav5_test_0182_gcd : Nat.gcd 15 25 = 5 := by
  norm_num [Nat.gcd]

theorem dav5_test_0182_step_0 : (25 : ℤ) = 1 * 15 + 10 := by
  norm_num

theorem dav5_test_0182_step_1 : (15 : ℤ) = 1 * 10 + 5 := by
  norm_num

theorem dav5_test_0182_step_2 : (10 : ℤ) = 2 * 5 + 0 := by
  norm_num

theorem dav5_test_0182_divides : (5 : ℤ) ∣ (-40 : ℤ) := by
  norm_num

theorem dav5_test_0182_conclusion : ∃ x y : ℤ, (-40 : ℤ) = (15 : ℤ) * x + (25 : ℤ) * y := by
  have hgcd : (Int.gcd (15 : ℤ) (25 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (15 : ℤ) (25 : ℤ) (-40 : ℤ)).2
  rw [hgcd]
  exact dav5_test_0182_divides

theorem dav5_test_0191_gcd : Nat.gcd 140 130 = 10 := by
  norm_num [Nat.gcd]

theorem dav5_test_0191_step_0 : (140 : ℤ) = 1 * 130 + 10 := by
  norm_num

theorem dav5_test_0191_step_1 : (130 : ℤ) = 13 * 10 + 0 := by
  norm_num

theorem dav5_test_0191_divides : ¬ (10 : ℤ) ∣ (91 : ℤ) := by
  norm_num

theorem dav5_test_0191_conclusion : ¬ (∃ x y : ℤ, (91 : ℤ) = (140 : ℤ) * x + (130 : ℤ) * y) := by
  have hgcd : (Int.gcd (140 : ℤ) (130 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (140 : ℤ) (130 : ℤ) (91 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0191_divides hd

theorem dav5_test_0193_gcd : Nat.gcd 143 77 = 11 := by
  norm_num [Nat.gcd]

theorem dav5_test_0193_step_0 : (143 : ℤ) = 1 * 77 + 66 := by
  norm_num

theorem dav5_test_0193_step_1 : (77 : ℤ) = 1 * 66 + 11 := by
  norm_num

theorem dav5_test_0193_step_2 : (66 : ℤ) = 6 * 11 + 0 := by
  norm_num

theorem dav5_test_0193_divides : ¬ (11 : ℤ) ∣ (-36 : ℤ) := by
  norm_num

theorem dav5_test_0193_conclusion : ¬ (∃ x y : ℤ, (-36 : ℤ) = (143 : ℤ) * x + (77 : ℤ) * y) := by
  have hgcd : (Int.gcd (143 : ℤ) (77 : ℤ) : ℤ) = 11 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (143 : ℤ) (77 : ℤ) (-36 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0193_divides hd

theorem dav5_test_0194_gcd : Nat.gcd 52 36 = 4 := by
  norm_num [Nat.gcd]

theorem dav5_test_0194_step_0 : (52 : ℤ) = 1 * 36 + 16 := by
  norm_num

theorem dav5_test_0194_step_1 : (36 : ℤ) = 2 * 16 + 4 := by
  norm_num

theorem dav5_test_0194_step_2 : (16 : ℤ) = 4 * 4 + 0 := by
  norm_num

theorem dav5_test_0194_divides : (4 : ℤ) ∣ (48 : ℤ) := by
  norm_num

theorem dav5_test_0194_conclusion : ∃ x y : ℤ, (48 : ℤ) = (52 : ℤ) * x + (36 : ℤ) * y := by
  have hgcd : (Int.gcd (52 : ℤ) (36 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (52 : ℤ) (36 : ℤ) (48 : ℤ)).2
  rw [hgcd]
  exact dav5_test_0194_divides

theorem dav5_test_0195_gcd : Nat.gcd 18 32 = 2 := by
  norm_num [Nat.gcd]

theorem dav5_test_0195_step_0 : (32 : ℤ) = 1 * 18 + 14 := by
  norm_num

theorem dav5_test_0195_step_1 : (18 : ℤ) = 1 * 14 + 4 := by
  norm_num

theorem dav5_test_0195_step_2 : (14 : ℤ) = 3 * 4 + 2 := by
  norm_num

theorem dav5_test_0195_step_3 : (4 : ℤ) = 2 * 2 + 0 := by
  norm_num

theorem dav5_test_0195_divides : ¬ (2 : ℤ) ∣ (-9 : ℤ) := by
  norm_num

theorem dav5_test_0195_conclusion : ¬ (∃ x y : ℤ, (-9 : ℤ) = (18 : ℤ) * x + (32 : ℤ) * y) := by
  have hgcd : (Int.gcd (18 : ℤ) (32 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (18 : ℤ) (32 : ℤ) (-9 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0195_divides hd

theorem dav5_test_0197_gcd : Nat.gcd 30 50 = 10 := by
  norm_num [Nat.gcd]

theorem dav5_test_0197_step_0 : (50 : ℤ) = 1 * 30 + 20 := by
  norm_num

theorem dav5_test_0197_step_1 : (30 : ℤ) = 1 * 20 + 10 := by
  norm_num

theorem dav5_test_0197_step_2 : (20 : ℤ) = 2 * 10 + 0 := by
  norm_num

theorem dav5_test_0197_divides : ¬ (10 : ℤ) ∣ (-32 : ℤ) := by
  norm_num

theorem dav5_test_0197_conclusion : ¬ (∃ x y : ℤ, (-32 : ℤ) = (30 : ℤ) * x + (50 : ℤ) * y) := by
  have hgcd : (Int.gcd (30 : ℤ) (50 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (30 : ℤ) (50 : ℤ) (-32 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav5_test_0197_divides hd

theorem dav5_test_0198_gcd : Nat.gcd 54 96 = 6 := by
  norm_num [Nat.gcd]

theorem dav5_test_0198_step_0 : (96 : ℤ) = 1 * 54 + 42 := by
  norm_num

theorem dav5_test_0198_step_1 : (54 : ℤ) = 1 * 42 + 12 := by
  norm_num

theorem dav5_test_0198_step_2 : (42 : ℤ) = 3 * 12 + 6 := by
  norm_num

theorem dav5_test_0198_step_3 : (12 : ℤ) = 2 * 6 + 0 := by
  norm_num

theorem dav5_test_0198_divides : (6 : ℤ) ∣ (-24 : ℤ) := by
  norm_num

theorem dav5_test_0198_conclusion : ∃ x y : ℤ, (-24 : ℤ) = (54 : ℤ) * x + (96 : ℤ) * y := by
  have hgcd : (Int.gcd (54 : ℤ) (96 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (54 : ℤ) (96 : ℤ) (-24 : ℤ)).2
  rw [hgcd]
  exact dav5_test_0198_divides

end AtomicClaimCertificates
