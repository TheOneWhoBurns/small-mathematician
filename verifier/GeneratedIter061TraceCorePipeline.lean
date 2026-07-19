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

theorem dav4_test_0010_gcd : Nat.gcd 525 485 = 5 := by
  norm_num [Nat.gcd]

theorem dav4_test_0010_step_0 : (525 : ℤ) = 1 * 485 + 40 := by
  norm_num

theorem dav4_test_0010_step_1 : (485 : ℤ) = 12 * 40 + 5 := by
  norm_num

theorem dav4_test_0010_step_2 : (40 : ℤ) = 8 * 5 + 0 := by
  norm_num

theorem dav4_test_0010_divides : (5 : ℤ) ∣ (-50 : ℤ) := by
  norm_num

theorem dav4_test_0010_conclusion : ∃ x y : ℤ, (-50 : ℤ) = (525 : ℤ) * x + (485 : ℤ) * y := by
  have hgcd : (Int.gcd (525 : ℤ) (485 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (525 : ℤ) (485 : ℤ) (-50 : ℤ)).2
  rw [hgcd]
  exact dav4_test_0010_divides

theorem dav4_test_0021_gcd : Nat.gcd 1118 650 = 26 := by
  norm_num [Nat.gcd]

theorem dav4_test_0021_step_0 : (1118 : ℤ) = 1 * 650 + 468 := by
  norm_num

theorem dav4_test_0021_step_1 : (650 : ℤ) = 1 * 468 + 182 := by
  norm_num

theorem dav4_test_0021_step_2 : (468 : ℤ) = 2 * 182 + 104 := by
  norm_num

theorem dav4_test_0021_step_3 : (182 : ℤ) = 1 * 104 + 78 := by
  norm_num

theorem dav4_test_0021_step_4 : (104 : ℤ) = 1 * 78 + 26 := by
  norm_num

theorem dav4_test_0021_step_5 : (78 : ℤ) = 3 * 26 + 0 := by
  norm_num

theorem dav4_test_0021_divides : ¬ (26 : ℤ) ∣ (487 : ℤ) := by
  norm_num

theorem dav4_test_0021_conclusion : ¬ (∃ x y : ℤ, (487 : ℤ) = (1118 : ℤ) * x + (650 : ℤ) * y) := by
  have hgcd : (Int.gcd (1118 : ℤ) (650 : ℤ) : ℤ) = 26 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (1118 : ℤ) (650 : ℤ) (487 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav4_test_0021_divides hd

theorem dav4_test_0031_gcd : Nat.gcd 204 326 = 2 := by
  norm_num [Nat.gcd]

theorem dav4_test_0031_step_0 : (326 : ℤ) = 1 * 204 + 122 := by
  norm_num

theorem dav4_test_0031_step_1 : (204 : ℤ) = 1 * 122 + 82 := by
  norm_num

theorem dav4_test_0031_step_2 : (122 : ℤ) = 1 * 82 + 40 := by
  norm_num

theorem dav4_test_0031_step_3 : (82 : ℤ) = 2 * 40 + 2 := by
  norm_num

theorem dav4_test_0031_step_4 : (40 : ℤ) = 20 * 2 + 0 := by
  norm_num

theorem dav4_test_0031_divides : ¬ (2 : ℤ) ∣ (19 : ℤ) := by
  norm_num

theorem dav4_test_0031_conclusion : ¬ (∃ x y : ℤ, (19 : ℤ) = (204 : ℤ) * x + (326 : ℤ) * y) := by
  have hgcd : (Int.gcd (204 : ℤ) (326 : ℤ) : ℤ) = 2 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (204 : ℤ) (326 : ℤ) (19 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav4_test_0031_divides hd

theorem dav4_test_0054_gcd : Nat.gcd 940 1020 = 20 := by
  norm_num [Nat.gcd]

theorem dav4_test_0054_step_0 : (1020 : ℤ) = 1 * 940 + 80 := by
  norm_num

theorem dav4_test_0054_step_1 : (940 : ℤ) = 11 * 80 + 60 := by
  norm_num

theorem dav4_test_0054_step_2 : (80 : ℤ) = 1 * 60 + 20 := by
  norm_num

theorem dav4_test_0054_step_3 : (60 : ℤ) = 3 * 20 + 0 := by
  norm_num

theorem dav4_test_0054_divides : (20 : ℤ) ∣ (-500 : ℤ) := by
  norm_num

theorem dav4_test_0054_conclusion : ∃ x y : ℤ, (-500 : ℤ) = (940 : ℤ) * x + (1020 : ℤ) * y := by
  have hgcd : (Int.gcd (940 : ℤ) (1020 : ℤ) : ℤ) = 20 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (940 : ℤ) (1020 : ℤ) (-500 : ℤ)).2
  rw [hgcd]
  exact dav4_test_0054_divides

theorem dav4_test_0084_gcd : Nat.gcd 120 272 = 8 := by
  norm_num [Nat.gcd]

theorem dav4_test_0084_step_0 : (272 : ℤ) = 2 * 120 + 32 := by
  norm_num

theorem dav4_test_0084_step_1 : (120 : ℤ) = 3 * 32 + 24 := by
  norm_num

theorem dav4_test_0084_step_2 : (32 : ℤ) = 1 * 24 + 8 := by
  norm_num

theorem dav4_test_0084_step_3 : (24 : ℤ) = 3 * 8 + 0 := by
  norm_num

theorem dav4_test_0084_divides : (8 : ℤ) ∣ (-192 : ℤ) := by
  norm_num

theorem dav4_test_0084_conclusion : ∃ x y : ℤ, (-192 : ℤ) = (120 : ℤ) * x + (272 : ℤ) * y := by
  have hgcd : (Int.gcd (120 : ℤ) (272 : ℤ) : ℤ) = 8 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (120 : ℤ) (272 : ℤ) (-192 : ℤ)).2
  rw [hgcd]
  exact dav4_test_0084_divides

theorem dav4_test_0104_gcd : Nat.gcd 1140 585 = 15 := by
  norm_num [Nat.gcd]

theorem dav4_test_0104_step_0 : (1140 : ℤ) = 1 * 585 + 555 := by
  norm_num

theorem dav4_test_0104_step_1 : (585 : ℤ) = 1 * 555 + 30 := by
  norm_num

theorem dav4_test_0104_step_2 : (555 : ℤ) = 18 * 30 + 15 := by
  norm_num

theorem dav4_test_0104_step_3 : (30 : ℤ) = 2 * 15 + 0 := by
  norm_num

theorem dav4_test_0104_divides : (15 : ℤ) ∣ (-225 : ℤ) := by
  norm_num

theorem dav4_test_0104_conclusion : ∃ x y : ℤ, (-225 : ℤ) = (1140 : ℤ) * x + (585 : ℤ) * y := by
  have hgcd : (Int.gcd (1140 : ℤ) (585 : ℤ) : ℤ) = 15 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (1140 : ℤ) (585 : ℤ) (-225 : ℤ)).2
  rw [hgcd]
  exact dav4_test_0104_divides

theorem dav4_test_0125_gcd : Nat.gcd 1335 930 = 15 := by
  norm_num [Nat.gcd]

theorem dav4_test_0125_step_0 : (1335 : ℤ) = 1 * 930 + 405 := by
  norm_num

theorem dav4_test_0125_step_1 : (930 : ℤ) = 2 * 405 + 120 := by
  norm_num

theorem dav4_test_0125_step_2 : (405 : ℤ) = 3 * 120 + 45 := by
  norm_num

theorem dav4_test_0125_step_3 : (120 : ℤ) = 2 * 45 + 30 := by
  norm_num

theorem dav4_test_0125_step_4 : (45 : ℤ) = 1 * 30 + 15 := by
  norm_num

theorem dav4_test_0125_step_5 : (30 : ℤ) = 2 * 15 + 0 := by
  norm_num

theorem dav4_test_0125_divides : ¬ (15 : ℤ) ∣ (-352 : ℤ) := by
  norm_num

theorem dav4_test_0125_conclusion : ¬ (∃ x y : ℤ, (-352 : ℤ) = (1335 : ℤ) * x + (930 : ℤ) * y) := by
  have hgcd : (Int.gcd (1335 : ℤ) (930 : ℤ) : ℤ) = 15 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (1335 : ℤ) (930 : ℤ) (-352 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav4_test_0125_divides hd

theorem dav4_test_0144_gcd : Nat.gcd 1026 846 = 18 := by
  norm_num [Nat.gcd]

theorem dav4_test_0144_step_0 : (1026 : ℤ) = 1 * 846 + 180 := by
  norm_num

theorem dav4_test_0144_step_1 : (846 : ℤ) = 4 * 180 + 126 := by
  norm_num

theorem dav4_test_0144_step_2 : (180 : ℤ) = 1 * 126 + 54 := by
  norm_num

theorem dav4_test_0144_step_3 : (126 : ℤ) = 2 * 54 + 18 := by
  norm_num

theorem dav4_test_0144_step_4 : (54 : ℤ) = 3 * 18 + 0 := by
  norm_num

theorem dav4_test_0144_divides : (18 : ℤ) ∣ (288 : ℤ) := by
  norm_num

theorem dav4_test_0144_conclusion : ∃ x y : ℤ, (288 : ℤ) = (1026 : ℤ) * x + (846 : ℤ) * y := by
  have hgcd : (Int.gcd (1026 : ℤ) (846 : ℤ) : ℤ) = 18 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (1026 : ℤ) (846 : ℤ) (288 : ℤ)).2
  rw [hgcd]
  exact dav4_test_0144_divides

theorem dav4_test_0161_gcd : Nat.gcd 625 680 = 5 := by
  norm_num [Nat.gcd]

theorem dav4_test_0161_step_0 : (680 : ℤ) = 1 * 625 + 55 := by
  norm_num

theorem dav4_test_0161_step_1 : (625 : ℤ) = 11 * 55 + 20 := by
  norm_num

theorem dav4_test_0161_step_2 : (55 : ℤ) = 2 * 20 + 15 := by
  norm_num

theorem dav4_test_0161_step_3 : (20 : ℤ) = 1 * 15 + 5 := by
  norm_num

theorem dav4_test_0161_step_4 : (15 : ℤ) = 3 * 5 + 0 := by
  norm_num

theorem dav4_test_0161_divides : ¬ (5 : ℤ) ∣ (8 : ℤ) := by
  norm_num

theorem dav4_test_0161_conclusion : ¬ (∃ x y : ℤ, (8 : ℤ) = (625 : ℤ) * x + (680 : ℤ) * y) := by
  have hgcd : (Int.gcd (625 : ℤ) (680 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (625 : ℤ) (680 : ℤ) (8 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav4_test_0161_divides hd

theorem dav4_test_0164_gcd : Nat.gcd 2478 4263 = 21 := by
  norm_num [Nat.gcd]

theorem dav4_test_0164_step_0 : (4263 : ℤ) = 1 * 2478 + 1785 := by
  norm_num

theorem dav4_test_0164_step_1 : (2478 : ℤ) = 1 * 1785 + 693 := by
  norm_num

theorem dav4_test_0164_step_2 : (1785 : ℤ) = 2 * 693 + 399 := by
  norm_num

theorem dav4_test_0164_step_3 : (693 : ℤ) = 1 * 399 + 294 := by
  norm_num

theorem dav4_test_0164_step_4 : (399 : ℤ) = 1 * 294 + 105 := by
  norm_num

theorem dav4_test_0164_step_5 : (294 : ℤ) = 2 * 105 + 84 := by
  norm_num

theorem dav4_test_0164_step_6 : (105 : ℤ) = 1 * 84 + 21 := by
  norm_num

theorem dav4_test_0164_step_7 : (84 : ℤ) = 4 * 21 + 0 := by
  norm_num

theorem dav4_test_0164_divides : (21 : ℤ) ∣ (-84 : ℤ) := by
  norm_num

theorem dav4_test_0164_conclusion : ∃ x y : ℤ, (-84 : ℤ) = (2478 : ℤ) * x + (4263 : ℤ) * y := by
  have hgcd : (Int.gcd (2478 : ℤ) (4263 : ℤ) : ℤ) = 21 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (2478 : ℤ) (4263 : ℤ) (-84 : ℤ)).2
  rw [hgcd]
  exact dav4_test_0164_divides

theorem dav4_test_0166_gcd : Nat.gcd 25 455 = 5 := by
  norm_num [Nat.gcd]

theorem dav4_test_0166_step_0 : (455 : ℤ) = 18 * 25 + 5 := by
  norm_num

theorem dav4_test_0166_step_1 : (25 : ℤ) = 5 * 5 + 0 := by
  norm_num

theorem dav4_test_0166_divides : (5 : ℤ) ∣ (30 : ℤ) := by
  norm_num

theorem dav4_test_0166_conclusion : ∃ x y : ℤ, (30 : ℤ) = (25 : ℤ) * x + (455 : ℤ) * y := by
  have hgcd : (Int.gcd (25 : ℤ) (455 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (25 : ℤ) (455 : ℤ) (30 : ℤ)).2
  rw [hgcd]
  exact dav4_test_0166_divides

theorem dav4_test_0177_gcd : Nat.gcd 96 204 = 12 := by
  norm_num [Nat.gcd]

theorem dav4_test_0177_step_0 : (204 : ℤ) = 2 * 96 + 12 := by
  norm_num

theorem dav4_test_0177_step_1 : (96 : ℤ) = 8 * 12 + 0 := by
  norm_num

theorem dav4_test_0177_divides : ¬ (12 : ℤ) ∣ (160 : ℤ) := by
  norm_num

theorem dav4_test_0177_conclusion : ¬ (∃ x y : ℤ, (160 : ℤ) = (96 : ℤ) * x + (204 : ℤ) * y) := by
  have hgcd : (Int.gcd (96 : ℤ) (204 : ℤ) : ℤ) = 12 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (96 : ℤ) (204 : ℤ) (160 : ℤ)).1 h
  rw [hgcd] at hd
  exact dav4_test_0177_divides hd

end AtomicClaimCertificates
