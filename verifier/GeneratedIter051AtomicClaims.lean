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

theorem vpl_v1_paraphrase_diophantine_solvability_008_533313dcbb_gcd : Nat.gcd 105 145 = 5 := by
  norm_num [Nat.gcd]

theorem vpl_v1_paraphrase_diophantine_solvability_008_533313dcbb_divides : (5 : ℤ) ∣ (35 : ℤ) := by
  norm_num

theorem vpl_v1_paraphrase_diophantine_solvability_008_533313dcbb_conclusion : ∃ x y : ℤ, (35 : ℤ) = (105 : ℤ) * x + (145 : ℤ) * y := by
  have hgcd : (Int.gcd (105 : ℤ) (145 : ℤ) : ℤ) = 5 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (105 : ℤ) (145 : ℤ) (35 : ℤ)).2
  rw [hgcd]
  exact vpl_v1_paraphrase_diophantine_solvability_008_533313dcbb_divides

theorem vpl_v1_paraphrase_diophantine_solvability_009_253eeb8186_gcd : Nat.gcd 133 119 = 7 := by
  norm_num [Nat.gcd]

theorem vpl_v1_paraphrase_diophantine_solvability_009_253eeb8186_divides : ¬ (7 : ℤ) ∣ (15 : ℤ) := by
  norm_num

theorem vpl_v1_paraphrase_diophantine_solvability_009_253eeb8186_conclusion : ¬ (∃ x y : ℤ, (15 : ℤ) = (133 : ℤ) * x + (119 : ℤ) * y) := by
  have hgcd : (Int.gcd (133 : ℤ) (119 : ℤ) : ℤ) = 7 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (133 : ℤ) (119 : ℤ) (15 : ℤ)).1 h
  rw [hgcd] at hd
  exact vpl_v1_paraphrase_diophantine_solvability_009_253eeb8186_divides hd

theorem vpl_v1_paraphrase_diophantine_solvability_011_b8e53db05d_gcd : Nat.gcd 121 264 = 11 := by
  norm_num [Nat.gcd]

theorem vpl_v1_paraphrase_diophantine_solvability_011_b8e53db05d_divides : (11 : ℤ) ∣ (-66 : ℤ) := by
  norm_num

theorem vpl_v1_paraphrase_diophantine_solvability_011_b8e53db05d_conclusion : ∃ x y : ℤ, (-66 : ℤ) = (121 : ℤ) * x + (264 : ℤ) * y := by
  have hgcd : (Int.gcd (121 : ℤ) (264 : ℤ) : ℤ) = 11 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (121 : ℤ) (264 : ℤ) (-66 : ℤ)).2
  rw [hgcd]
  exact vpl_v1_paraphrase_diophantine_solvability_011_b8e53db05d_divides

theorem vpl_v1_paraphrase_diophantine_solvability_014_5814fdf22b_gcd : Nat.gcd 250 280 = 10 := by
  norm_num [Nat.gcd]

theorem vpl_v1_paraphrase_diophantine_solvability_014_5814fdf22b_divides : (10 : ℤ) ∣ (-30 : ℤ) := by
  norm_num

theorem vpl_v1_paraphrase_diophantine_solvability_014_5814fdf22b_conclusion : ∃ x y : ℤ, (-30 : ℤ) = (250 : ℤ) * x + (280 : ℤ) * y := by
  have hgcd : (Int.gcd (250 : ℤ) (280 : ℤ) : ℤ) = 10 := by norm_num [Int.gcd]
  apply (linearCombinationIffGcdDvd (250 : ℤ) (280 : ℤ) (-30 : ℤ)).2
  rw [hgcd]
  exact vpl_v1_paraphrase_diophantine_solvability_014_5814fdf22b_divides

theorem vpl_v1_paraphrase_diophantine_solvability_015_a3c5f2989e_gcd : Nat.gcd 171 288 = 9 := by
  norm_num [Nat.gcd]

theorem vpl_v1_paraphrase_diophantine_solvability_015_a3c5f2989e_divides : ¬ (9 : ℤ) ∣ (-52 : ℤ) := by
  norm_num

theorem vpl_v1_paraphrase_diophantine_solvability_015_a3c5f2989e_conclusion : ¬ (∃ x y : ℤ, (-52 : ℤ) = (171 : ℤ) * x + (288 : ℤ) * y) := by
  have hgcd : (Int.gcd (171 : ℤ) (288 : ℤ) : ℤ) = 9 := by norm_num [Int.gcd]
  intro h
  have hd := (linearCombinationIffGcdDvd (171 : ℤ) (288 : ℤ) (-52 : ℤ)).1 h
  rw [hgcd] at hd
  exact vpl_v1_paraphrase_diophantine_solvability_015_a3c5f2989e_divides hd

end AtomicClaimCertificates
