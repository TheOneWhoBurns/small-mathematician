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

theorem scale1000_test_0003_gcd : Nat.gcd 399 553 = 7 := by
  norm_num [Nat.gcd]

theorem scale1000_test_0003_step_0 : (553 : ℤ) = 1 * 399 + 154 := by
  norm_num

theorem scale1000_test_0003_step_1 : (399 : ℤ) = 2 * 154 + 91 := by
  norm_num

theorem scale1000_test_0003_step_2 : (154 : ℤ) = 1 * 91 + 63 := by
  norm_num

theorem scale1000_test_0003_step_3 : (91 : ℤ) = 1 * 63 + 28 := by
  norm_num

theorem scale1000_test_0003_step_4 : (63 : ℤ) = 2 * 28 + 7 := by
  norm_num

theorem scale1000_test_0003_step_5 : (28 : ℤ) = 4 * 7 + 0 := by
  norm_num

theorem scale1000_test_0003_divides : ¬ (7 : ℤ) ∣ (152 : ℤ) := by
  norm_num

theorem scale1000_test_0003_conclusion : ¬ (∃ x y : ℤ, (152 : ℤ) = (399 : ℤ) * x + (553 : ℤ) * y) := by
  have hgcd : (Int.gcd (399 : ℤ) (553 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (399 : ℤ) (553 : ℤ) (152 : ℤ)).1 h
  rw [hgcd] at hd
  exact scale1000_test_0003_divides hd

theorem scale1000_test_0025_gcd : Nat.gcd 820 120 = 20 := by
  norm_num [Nat.gcd]

theorem scale1000_test_0025_step_0 : (820 : ℤ) = 6 * 120 + 100 := by
  norm_num

theorem scale1000_test_0025_step_1 : (120 : ℤ) = 1 * 100 + 20 := by
  norm_num

theorem scale1000_test_0025_step_2 : (100 : ℤ) = 5 * 20 + 0 := by
  norm_num

theorem scale1000_test_0025_divides : ¬ (20 : ℤ) ∣ (519 : ℤ) := by
  norm_num

theorem scale1000_test_0025_conclusion : ¬ (∃ x y : ℤ, (519 : ℤ) = (820 : ℤ) * x + (120 : ℤ) * y) := by
  have hgcd : (Int.gcd (820 : ℤ) (120 : ℤ) : ℤ) = 20 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (820 : ℤ) (120 : ℤ) (519 : ℤ)).1 h
  rw [hgcd] at hd
  exact scale1000_test_0025_divides hd

theorem scale1000_test_0026_gcd : Nat.gcd 500 808 = 4 := by
  norm_num [Nat.gcd]

theorem scale1000_test_0026_step_0 : (808 : ℤ) = 1 * 500 + 308 := by
  norm_num

theorem scale1000_test_0026_step_1 : (500 : ℤ) = 1 * 308 + 192 := by
  norm_num

theorem scale1000_test_0026_step_2 : (308 : ℤ) = 1 * 192 + 116 := by
  norm_num

theorem scale1000_test_0026_step_3 : (192 : ℤ) = 1 * 116 + 76 := by
  norm_num

theorem scale1000_test_0026_step_4 : (116 : ℤ) = 1 * 76 + 40 := by
  norm_num

theorem scale1000_test_0026_step_5 : (76 : ℤ) = 1 * 40 + 36 := by
  norm_num

theorem scale1000_test_0026_step_6 : (40 : ℤ) = 1 * 36 + 4 := by
  norm_num

theorem scale1000_test_0026_step_7 : (36 : ℤ) = 9 * 4 + 0 := by
  norm_num

theorem scale1000_test_0026_divides : (4 : ℤ) ∣ (-92 : ℤ) := by
  norm_num

theorem scale1000_test_0026_conclusion : ∃ x y : ℤ, (-92 : ℤ) = (500 : ℤ) * x + (808 : ℤ) * y := by
  have hgcd : (Int.gcd (500 : ℤ) (808 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (500 : ℤ) (808 : ℤ) (-92 : ℤ)).2
  simpa [hgcd] using scale1000_test_0026_divides

theorem scale1000_test_0033_gcd : Nat.gcd 931 342 = 19 := by
  norm_num [Nat.gcd]

theorem scale1000_test_0033_step_0 : (931 : ℤ) = 2 * 342 + 247 := by
  norm_num

theorem scale1000_test_0033_step_1 : (342 : ℤ) = 1 * 247 + 95 := by
  norm_num

theorem scale1000_test_0033_step_2 : (247 : ℤ) = 2 * 95 + 57 := by
  norm_num

theorem scale1000_test_0033_step_3 : (95 : ℤ) = 1 * 57 + 38 := by
  norm_num

theorem scale1000_test_0033_step_4 : (57 : ℤ) = 1 * 38 + 19 := by
  norm_num

theorem scale1000_test_0033_step_5 : (38 : ℤ) = 2 * 19 + 0 := by
  norm_num

theorem scale1000_test_0033_divides : ¬ (19 : ℤ) ∣ (250 : ℤ) := by
  norm_num

theorem scale1000_test_0033_conclusion : ¬ (∃ x y : ℤ, (250 : ℤ) = (931 : ℤ) * x + (342 : ℤ) * y) := by
  have hgcd : (Int.gcd (931 : ℤ) (342 : ℤ) : ℤ) = 19 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (931 : ℤ) (342 : ℤ) (250 : ℤ)).1 h
  rw [hgcd] at hd
  exact scale1000_test_0033_divides hd

theorem scale1000_test_0040_gcd : Nat.gcd 800 512 = 32 := by
  norm_num [Nat.gcd]

theorem scale1000_test_0040_step_0 : (800 : ℤ) = 1 * 512 + 288 := by
  norm_num

theorem scale1000_test_0040_step_1 : (512 : ℤ) = 1 * 288 + 224 := by
  norm_num

theorem scale1000_test_0040_step_2 : (288 : ℤ) = 1 * 224 + 64 := by
  norm_num

theorem scale1000_test_0040_step_3 : (224 : ℤ) = 3 * 64 + 32 := by
  norm_num

theorem scale1000_test_0040_step_4 : (64 : ℤ) = 2 * 32 + 0 := by
  norm_num

theorem scale1000_test_0040_divides : (32 : ℤ) ∣ (-128 : ℤ) := by
  norm_num

theorem scale1000_test_0040_conclusion : ∃ x y : ℤ, (-128 : ℤ) = (800 : ℤ) * x + (512 : ℤ) * y := by
  have hgcd : (Int.gcd (800 : ℤ) (512 : ℤ) : ℤ) = 32 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (800 : ℤ) (512 : ℤ) (-128 : ℤ)).2
  simpa [hgcd] using scale1000_test_0040_divides

theorem scale1000_test_0048_gcd : Nat.gcd 460 788 = 4 := by
  norm_num [Nat.gcd]

theorem scale1000_test_0048_step_0 : (788 : ℤ) = 1 * 460 + 328 := by
  norm_num

theorem scale1000_test_0048_step_1 : (460 : ℤ) = 1 * 328 + 132 := by
  norm_num

theorem scale1000_test_0048_step_2 : (328 : ℤ) = 2 * 132 + 64 := by
  norm_num

theorem scale1000_test_0048_step_3 : (132 : ℤ) = 2 * 64 + 4 := by
  norm_num

theorem scale1000_test_0048_step_4 : (64 : ℤ) = 16 * 4 + 0 := by
  norm_num

theorem scale1000_test_0048_divides : (4 : ℤ) ∣ (96 : ℤ) := by
  norm_num

theorem scale1000_test_0048_conclusion : ∃ x y : ℤ, (96 : ℤ) = (460 : ℤ) * x + (788 : ℤ) * y := by
  have hgcd : (Int.gcd (460 : ℤ) (788 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (460 : ℤ) (788 : ℤ) (96 : ℤ)).2
  simpa [hgcd] using scale1000_test_0048_divides

theorem scale1000_test_0054_gcd : Nat.gcd 539 182 = 7 := by
  norm_num [Nat.gcd]

theorem scale1000_test_0054_step_0 : (539 : ℤ) = 2 * 182 + 175 := by
  norm_num

theorem scale1000_test_0054_step_1 : (182 : ℤ) = 1 * 175 + 7 := by
  norm_num

theorem scale1000_test_0054_step_2 : (175 : ℤ) = 25 * 7 + 0 := by
  norm_num

theorem scale1000_test_0054_divides : (7 : ℤ) ∣ (-7 : ℤ) := by
  norm_num

theorem scale1000_test_0054_conclusion : ∃ x y : ℤ, (-7 : ℤ) = (539 : ℤ) * x + (182 : ℤ) * y := by
  have hgcd : (Int.gcd (539 : ℤ) (182 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (539 : ℤ) (182 : ℤ) (-7 : ℤ)).2
  simpa [hgcd] using scale1000_test_0054_divides

theorem scale1000_test_0055_gcd : Nat.gcd 788 560 = 4 := by
  norm_num [Nat.gcd]

theorem scale1000_test_0055_step_0 : (788 : ℤ) = 1 * 560 + 228 := by
  norm_num

theorem scale1000_test_0055_step_1 : (560 : ℤ) = 2 * 228 + 104 := by
  norm_num

theorem scale1000_test_0055_step_2 : (228 : ℤ) = 2 * 104 + 20 := by
  norm_num

theorem scale1000_test_0055_step_3 : (104 : ℤ) = 5 * 20 + 4 := by
  norm_num

theorem scale1000_test_0055_step_4 : (20 : ℤ) = 5 * 4 + 0 := by
  norm_num

theorem scale1000_test_0055_divides : ¬ (4 : ℤ) ∣ (-50 : ℤ) := by
  norm_num

theorem scale1000_test_0055_conclusion : ¬ (∃ x y : ℤ, (-50 : ℤ) = (788 : ℤ) * x + (560 : ℤ) * y) := by
  have hgcd : (Int.gcd (788 : ℤ) (560 : ℤ) : ℤ) = 4 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (788 : ℤ) (560 : ℤ) (-50 : ℤ)).1 h
  rw [hgcd] at hd
  exact scale1000_test_0055_divides hd

theorem scale1000_test_0064_gcd : Nat.gcd 738 276 = 6 := by
  norm_num [Nat.gcd]

theorem scale1000_test_0064_step_0 : (738 : ℤ) = 2 * 276 + 186 := by
  norm_num

theorem scale1000_test_0064_step_1 : (276 : ℤ) = 1 * 186 + 90 := by
  norm_num

theorem scale1000_test_0064_step_2 : (186 : ℤ) = 2 * 90 + 6 := by
  norm_num

theorem scale1000_test_0064_step_3 : (90 : ℤ) = 15 * 6 + 0 := by
  norm_num

theorem scale1000_test_0064_divides : (6 : ℤ) ∣ (-6 : ℤ) := by
  norm_num

theorem scale1000_test_0064_conclusion : ∃ x y : ℤ, (-6 : ℤ) = (738 : ℤ) * x + (276 : ℤ) * y := by
  have hgcd : (Int.gcd (738 : ℤ) (276 : ℤ) : ℤ) = 6 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (738 : ℤ) (276 : ℤ) (-6 : ℤ)).2
  simpa [hgcd] using scale1000_test_0064_divides

theorem scale1000_test_0077_gcd : Nat.gcd 564 504 = 12 := by
  norm_num [Nat.gcd]

theorem scale1000_test_0077_step_0 : (564 : ℤ) = 1 * 504 + 60 := by
  norm_num

theorem scale1000_test_0077_step_1 : (504 : ℤ) = 8 * 60 + 24 := by
  norm_num

theorem scale1000_test_0077_step_2 : (60 : ℤ) = 2 * 24 + 12 := by
  norm_num

theorem scale1000_test_0077_step_3 : (24 : ℤ) = 2 * 12 + 0 := by
  norm_num

theorem scale1000_test_0077_divides : ¬ (12 : ℤ) ∣ (106 : ℤ) := by
  norm_num

theorem scale1000_test_0077_conclusion : ¬ (∃ x y : ℤ, (106 : ℤ) = (564 : ℤ) * x + (504 : ℤ) * y) := by
  have hgcd : (Int.gcd (564 : ℤ) (504 : ℤ) : ℤ) = 12 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (564 : ℤ) (504 : ℤ) (106 : ℤ)).1 h
  rw [hgcd] at hd
  exact scale1000_test_0077_divides hd

end AtomicClaimCertificates
