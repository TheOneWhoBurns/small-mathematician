import VerifiedPlanHelpers

namespace VerifiedPlanCertificates

open Polynomial VerifiedPlanHelpers

theorem vp_vpl_v1_valid_polynomial_value_obstruction_000_fee04bd3af_differences : (((-10) - 2 : ℤ) = (-12)) ∧ ((63 - 2 : ℤ) = 61) := by
  norm_num

theorem vp_vpl_v1_valid_polynomial_value_obstruction_000_fee04bd3af_remainder : (61 : ℤ) % 12 = 1 := by
  norm_num

theorem vp_vpl_v1_valid_polynomial_value_obstruction_000_fee04bd3af : ¬ (∃ P : Polynomial ℤ, P.eval 2 = 2 ∧ P.eval (-10) = 63) := by
  apply no_polynomial_with_values_of_not_dvd
  norm_num


theorem vp_vpl_v1_valid_polynomial_value_obstruction_001_fd78815aad_differences : ((11 - 14 : ℤ) = (-3)) ∧ ((19 - 29 : ℤ) = (-10)) := by
  norm_num

theorem vp_vpl_v1_valid_polynomial_value_obstruction_001_fd78815aad_remainder : ((-10) : ℤ) % 3 = 2 := by
  norm_num

theorem vp_vpl_v1_valid_polynomial_value_obstruction_001_fd78815aad : ¬ (∃ P : Polynomial ℤ, P.eval 14 = 29 ∧ P.eval 11 = 19) := by
  apply no_polynomial_with_values_of_not_dvd
  norm_num


theorem vp_vpl_v1_valid_polynomial_value_obstruction_002_226afbcf74_differences : ((3 - (-5) : ℤ) = 8) ∧ (((-121) - (-41) : ℤ) = (-80)) := by
  norm_num

theorem vp_vpl_v1_valid_polynomial_value_obstruction_002_226afbcf74_remainder : ((-80) : ℤ) % 8 = 0 := by
  norm_num

theorem vp_vpl_v1_valid_polynomial_value_obstruction_002_226afbcf74 : ∃ P : Polynomial ℤ, P.eval (-5) = (-41) ∧ P.eval 3 = (-121) := by
  refine ⟨linearPolynomialWitness (-10) (-5) (-41), ?_, ?_⟩ <;>
    norm_num [linearPolynomialWitness]


theorem vp_vpl_v1_valid_polynomial_value_obstruction_003_b14e123873_differences : (((-11) - 1 : ℤ) = (-12)) ∧ (((-76) - 9 : ℤ) = (-85)) := by
  norm_num

theorem vp_vpl_v1_valid_polynomial_value_obstruction_003_b14e123873_remainder : ((-85) : ℤ) % 12 = 11 := by
  norm_num

theorem vp_vpl_v1_valid_polynomial_value_obstruction_003_b14e123873 : ¬ (∃ P : Polynomial ℤ, P.eval 1 = 9 ∧ P.eval (-11) = (-76)) := by
  apply no_polynomial_with_values_of_not_dvd
  norm_num


theorem vp_vpl_v1_valid_polynomial_value_obstruction_004_41cacf4fe8_differences : ((6 - 4 : ℤ) = 2) ∧ ((57 - 51 : ℤ) = 6) := by
  norm_num

theorem vp_vpl_v1_valid_polynomial_value_obstruction_004_41cacf4fe8_remainder : (6 : ℤ) % 2 = 0 := by
  norm_num

theorem vp_vpl_v1_valid_polynomial_value_obstruction_004_41cacf4fe8 : ∃ P : Polynomial ℤ, P.eval 4 = 51 ∧ P.eval 6 = 57 := by
  refine ⟨linearPolynomialWitness 3 4 51, ?_, ?_⟩ <;>
    norm_num [linearPolynomialWitness]


theorem vp_vpl_v1_valid_polynomial_value_obstruction_005_7c10903c64_differences : (((-5) - 2 : ℤ) = (-7)) ∧ ((82 - 12 : ℤ) = 70) := by
  norm_num

theorem vp_vpl_v1_valid_polynomial_value_obstruction_005_7c10903c64_remainder : (70 : ℤ) % 7 = 0 := by
  norm_num

theorem vp_vpl_v1_valid_polynomial_value_obstruction_005_7c10903c64 : ∃ P : Polynomial ℤ, P.eval 2 = 12 ∧ P.eval (-5) = 82 := by
  refine ⟨linearPolynomialWitness (-10) 2 12, ?_, ?_⟩ <;>
    norm_num [linearPolynomialWitness]


theorem vp_vpl_v1_valid_polynomial_value_obstruction_006_83064b5791_differences : ((8 - (-3) : ℤ) = 11) ∧ ((83 - (-18) : ℤ) = 101) := by
  norm_num

theorem vp_vpl_v1_valid_polynomial_value_obstruction_006_83064b5791_remainder : (101 : ℤ) % 11 = 2 := by
  norm_num

theorem vp_vpl_v1_valid_polynomial_value_obstruction_006_83064b5791 : ¬ (∃ P : Polynomial ℤ, P.eval (-3) = (-18) ∧ P.eval 8 = 83) := by
  apply no_polynomial_with_values_of_not_dvd
  norm_num


theorem vp_vpl_v1_valid_polynomial_value_obstruction_007_7a92beb12d_differences : ((2 - (-9) : ℤ) = 11) ∧ (((-108) - (-27) : ℤ) = (-81)) := by
  norm_num

theorem vp_vpl_v1_valid_polynomial_value_obstruction_007_7a92beb12d_remainder : ((-81) : ℤ) % 11 = 7 := by
  norm_num

theorem vp_vpl_v1_valid_polynomial_value_obstruction_007_7a92beb12d : ¬ (∃ P : Polynomial ℤ, P.eval (-9) = (-27) ∧ P.eval 2 = (-108)) := by
  apply no_polynomial_with_values_of_not_dvd
  norm_num


theorem vp_vpl_v1_valid_polynomial_value_obstruction_008_043d6cafb9_differences : ((24 - 17 : ℤ) = 7) ∧ (((-7) - (-35) : ℤ) = 28) := by
  norm_num

theorem vp_vpl_v1_valid_polynomial_value_obstruction_008_043d6cafb9_remainder : (28 : ℤ) % 7 = 0 := by
  norm_num

theorem vp_vpl_v1_valid_polynomial_value_obstruction_008_043d6cafb9 : ∃ P : Polynomial ℤ, P.eval 17 = (-35) ∧ P.eval 24 = (-7) := by
  refine ⟨linearPolynomialWitness 4 17 (-35), ?_, ?_⟩ <;>
    norm_num [linearPolynomialWitness]


theorem vp_vpl_v1_valid_polynomial_value_obstruction_009_2fd289cbbc_differences : (((-18) - (-13) : ℤ) = (-5)) ∧ (((-63) - (-40) : ℤ) = (-23)) := by
  norm_num

theorem vp_vpl_v1_valid_polynomial_value_obstruction_009_2fd289cbbc_remainder : ((-23) : ℤ) % 5 = 2 := by
  norm_num

theorem vp_vpl_v1_valid_polynomial_value_obstruction_009_2fd289cbbc : ¬ (∃ P : Polynomial ℤ, P.eval (-13) = (-40) ∧ P.eval (-18) = (-63)) := by
  apply no_polynomial_with_values_of_not_dvd
  norm_num


theorem vp_vpl_v1_valid_diophantine_solvability_000_5e15db75df_gcd : Nat.gcd (24 : ℤ).natAbs (78 : ℤ).natAbs = 6 := by
  norm_num [Int.natAbs]

theorem vp_vpl_v1_valid_diophantine_solvability_000_5e15db75df : ¬ (∃ x y : ℤ, 24 * x + 78 * y = (-35)) := by
  apply no_diophantine_solution_of_common_dvd (g := 6)
  · norm_num
  · norm_num
  · norm_num


theorem vp_vpl_v1_valid_diophantine_solvability_001_2e9b40116c_gcd : Nat.gcd (156 : ℤ).natAbs (150 : ℤ).natAbs = 6 := by
  norm_num [Int.natAbs]

theorem vp_vpl_v1_valid_diophantine_solvability_001_2e9b40116c : ¬ (∃ x y : ℤ, 156 * x + 150 * y = (-35)) := by
  apply no_diophantine_solution_of_common_dvd (g := 6)
  · norm_num
  · norm_num
  · norm_num


theorem vp_vpl_v1_valid_diophantine_solvability_002_29e3c7be1f_gcd : Nat.gcd (100 : ℤ).natAbs (230 : ℤ).natAbs = 10 := by
  norm_num [Int.natAbs]

theorem vp_vpl_v1_valid_diophantine_solvability_002_29e3c7be1f_bezout : (100 : ℤ) * 7 + 230 * (-3) = 10 := by
  norm_num

theorem vp_vpl_v1_valid_diophantine_solvability_002_29e3c7be1f : ∃ x y : ℤ, 100 * x + 230 * y = 40 := by
  exact ⟨28, (-12), by norm_num⟩


theorem vp_vpl_v1_valid_diophantine_solvability_003_9310751c87_gcd : Nat.gcd (63 : ℤ).natAbs (207 : ℤ).natAbs = 9 := by
  norm_num [Int.natAbs]

theorem vp_vpl_v1_valid_diophantine_solvability_003_9310751c87 : ¬ (∃ x y : ℤ, 63 * x + 207 * y = 10) := by
  apply no_diophantine_solution_of_common_dvd (g := 9)
  · norm_num
  · norm_num
  · norm_num


theorem vp_vpl_v1_valid_diophantine_solvability_004_4c7edd7af6_gcd : Nat.gcd (203 : ℤ).natAbs (98 : ℤ).natAbs = 7 := by
  norm_num [Int.natAbs]

theorem vp_vpl_v1_valid_diophantine_solvability_004_4c7edd7af6_bezout : (203 : ℤ) * 1 + 98 * (-2) = 7 := by
  norm_num

theorem vp_vpl_v1_valid_diophantine_solvability_004_4c7edd7af6 : ∃ x y : ℤ, 203 * x + 98 * y = 42 := by
  exact ⟨6, (-12), by norm_num⟩


theorem vp_vpl_v1_valid_diophantine_solvability_005_248333b50f_gcd : Nat.gcd (272 : ℤ).natAbs (280 : ℤ).natAbs = 8 := by
  norm_num [Int.natAbs]

theorem vp_vpl_v1_valid_diophantine_solvability_005_248333b50f_bezout : (272 : ℤ) * (-1) + 280 * 1 = 8 := by
  norm_num

theorem vp_vpl_v1_valid_diophantine_solvability_005_248333b50f : ∃ x y : ℤ, 272 * x + 280 * y = (-72) := by
  exact ⟨9, (-9), by norm_num⟩


theorem vp_vpl_v1_valid_diophantine_solvability_006_096722e575_gcd : Nat.gcd (152 : ℤ).natAbs (224 : ℤ).natAbs = 8 := by
  norm_num [Int.natAbs]

theorem vp_vpl_v1_valid_diophantine_solvability_006_096722e575 : ¬ (∃ x y : ℤ, 152 * x + 224 * y = 30) := by
  apply no_diophantine_solution_of_common_dvd (g := 8)
  · norm_num
  · norm_num
  · norm_num


theorem vp_vpl_v1_valid_diophantine_solvability_007_943e168a94_gcd : Nat.gcd (143 : ℤ).natAbs (352 : ℤ).natAbs = 11 := by
  norm_num [Int.natAbs]

theorem vp_vpl_v1_valid_diophantine_solvability_007_943e168a94 : ¬ (∃ x y : ℤ, 143 * x + 352 * y = 81) := by
  apply no_diophantine_solution_of_common_dvd (g := 11)
  · norm_num
  · norm_num
  · norm_num


theorem vp_vpl_v1_valid_diophantine_solvability_008_ca41112ca0_gcd : Nat.gcd (20 : ℤ).natAbs (104 : ℤ).natAbs = 4 := by
  norm_num [Int.natAbs]

theorem vp_vpl_v1_valid_diophantine_solvability_008_ca41112ca0_bezout : (20 : ℤ) * (-5) + 104 * 1 = 4 := by
  norm_num

theorem vp_vpl_v1_valid_diophantine_solvability_008_ca41112ca0 : ∃ x y : ℤ, 20 * x + 104 * y = 36 := by
  exact ⟨(-45), 9, by norm_num⟩


theorem vp_vpl_v1_valid_diophantine_solvability_009_c8166720b3_gcd : Nat.gcd (120 : ℤ).natAbs (35 : ℤ).natAbs = 5 := by
  norm_num [Int.natAbs]

theorem vp_vpl_v1_valid_diophantine_solvability_009_c8166720b3 : ¬ (∃ x y : ℤ, 120 * x + 35 * y = 27) := by
  apply no_diophantine_solution_of_common_dvd (g := 5)
  · norm_num
  · norm_num
  · norm_num


theorem vp_vpl_v1_valid_modular_period_prime_filter_000_7d94d2bbe3_period : powResidue 5 11 5 = 1 := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_000_7d94d2bbe3_periodic (exponent : ℕ) :
    powResidue 5 11 (exponent + 5) = powResidue 5 11 exponent := by
  exact powResidue_add_period vp_vpl_v1_valid_modular_period_prime_filter_000_7d94d2bbe3_period

theorem vp_vpl_v1_valid_modular_period_prime_filter_000_7d94d2bbe3_minimal_period : properPeriodWitnesses 5 11 5 = [] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_000_7d94d2bbe3_classes : residueClasses 5 11 4 5 = [3] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_000_7d94d2bbe3 : residueClasses 5 11 4 5 = [3] := by
  exact vp_vpl_v1_valid_modular_period_prime_filter_000_7d94d2bbe3_classes


theorem vp_vpl_v1_valid_modular_period_prime_filter_001_138093dc21_period : powResidue 3 5 4 = 1 := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_001_138093dc21_periodic (exponent : ℕ) :
    powResidue 3 5 (exponent + 4) = powResidue 3 5 exponent := by
  exact powResidue_add_period vp_vpl_v1_valid_modular_period_prime_filter_001_138093dc21_period

theorem vp_vpl_v1_valid_modular_period_prime_filter_001_138093dc21_minimal_period : properPeriodWitnesses 3 5 4 = [] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_001_138093dc21_classes : residueClasses 3 5 1 4 = [0] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_001_138093dc21_prime_range : primesInClosedRange 2 27 = [2, 3, 5, 7, 11, 13, 17, 19, 23] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_001_138093dc21 : validPrimeExponents 3 5 1 2 27 = [] := by
  native_decide


theorem vp_vpl_v1_valid_modular_period_prime_filter_002_c1f12dd3e4_period : powResidue 11 19 3 = 1 := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_002_c1f12dd3e4_periodic (exponent : ℕ) :
    powResidue 11 19 (exponent + 3) = powResidue 11 19 exponent := by
  exact powResidue_add_period vp_vpl_v1_valid_modular_period_prime_filter_002_c1f12dd3e4_period

theorem vp_vpl_v1_valid_modular_period_prime_filter_002_c1f12dd3e4_minimal_period : properPeriodWitnesses 11 19 3 = [] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_002_c1f12dd3e4_classes : residueClasses 11 19 1 3 = [0] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_002_c1f12dd3e4 : residueClasses 11 19 1 3 = [0] := by
  exact vp_vpl_v1_valid_modular_period_prime_filter_002_c1f12dd3e4_classes


theorem vp_vpl_v1_valid_modular_period_prime_filter_003_0ffc9bc46b_period : powResidue 7 19 3 = 1 := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_003_0ffc9bc46b_periodic (exponent : ℕ) :
    powResidue 7 19 (exponent + 3) = powResidue 7 19 exponent := by
  exact powResidue_add_period vp_vpl_v1_valid_modular_period_prime_filter_003_0ffc9bc46b_period

theorem vp_vpl_v1_valid_modular_period_prime_filter_003_0ffc9bc46b_minimal_period : properPeriodWitnesses 7 19 3 = [] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_003_0ffc9bc46b_classes : residueClasses 7 19 11 3 = [2] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_003_0ffc9bc46b : residueClasses 7 19 11 3 = [2] := by
  exact vp_vpl_v1_valid_modular_period_prime_filter_003_0ffc9bc46b_classes


theorem vp_vpl_v1_valid_modular_period_prime_filter_004_f1217b1fb2_period : powResidue 16 19 9 = 1 := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_004_f1217b1fb2_periodic (exponent : ℕ) :
    powResidue 16 19 (exponent + 9) = powResidue 16 19 exponent := by
  exact powResidue_add_period vp_vpl_v1_valid_modular_period_prime_filter_004_f1217b1fb2_period

theorem vp_vpl_v1_valid_modular_period_prime_filter_004_f1217b1fb2_minimal_period : properPeriodWitnesses 16 19 9 = [] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_004_f1217b1fb2_classes : residueClasses 16 19 6 9 = [8] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_004_f1217b1fb2_prime_range : primesInClosedRange 2 52 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_004_f1217b1fb2 : validPrimeExponents 16 19 6 2 52 = [17] := by
  native_decide


theorem vp_vpl_v1_valid_modular_period_prime_filter_005_5a97079c5c_period : powResidue 7 17 16 = 1 := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_005_5a97079c5c_periodic (exponent : ℕ) :
    powResidue 7 17 (exponent + 16) = powResidue 7 17 exponent := by
  exact powResidue_add_period vp_vpl_v1_valid_modular_period_prime_filter_005_5a97079c5c_period

theorem vp_vpl_v1_valid_modular_period_prime_filter_005_5a97079c5c_minimal_period : properPeriodWitnesses 7 17 16 = [] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_005_5a97079c5c_classes : residueClasses 7 17 14 16 = [11] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_005_5a97079c5c : residueClasses 7 17 14 16 = [11] := by
  exact vp_vpl_v1_valid_modular_period_prime_filter_005_5a97079c5c_classes


theorem vp_vpl_v1_valid_modular_period_prime_filter_006_4e0fbbda6f_period : powResidue 9 13 3 = 1 := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_006_4e0fbbda6f_periodic (exponent : ℕ) :
    powResidue 9 13 (exponent + 3) = powResidue 9 13 exponent := by
  exact powResidue_add_period vp_vpl_v1_valid_modular_period_prime_filter_006_4e0fbbda6f_period

theorem vp_vpl_v1_valid_modular_period_prime_filter_006_4e0fbbda6f_minimal_period : properPeriodWitnesses 9 13 3 = [] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_006_4e0fbbda6f_classes : residueClasses 9 13 9 3 = [1] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_006_4e0fbbda6f : residueClasses 9 13 9 3 = [1] := by
  exact vp_vpl_v1_valid_modular_period_prime_filter_006_4e0fbbda6f_classes


theorem vp_vpl_v1_valid_modular_period_prime_filter_007_86dec444bc_period : powResidue 3 5 4 = 1 := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_007_86dec444bc_periodic (exponent : ℕ) :
    powResidue 3 5 (exponent + 4) = powResidue 3 5 exponent := by
  exact powResidue_add_period vp_vpl_v1_valid_modular_period_prime_filter_007_86dec444bc_period

theorem vp_vpl_v1_valid_modular_period_prime_filter_007_86dec444bc_minimal_period : properPeriodWitnesses 3 5 4 = [] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_007_86dec444bc_classes : residueClasses 3 5 2 4 = [3] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_007_86dec444bc_prime_range : primesInClosedRange 2 27 = [2, 3, 5, 7, 11, 13, 17, 19, 23] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_007_86dec444bc : validPrimeExponents 3 5 2 2 27 = [3, 7, 11, 19, 23] := by
  native_decide


theorem vp_vpl_v1_valid_modular_period_prime_filter_008_a46a3aca58_period : powResidue 14 17 16 = 1 := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_008_a46a3aca58_periodic (exponent : ℕ) :
    powResidue 14 17 (exponent + 16) = powResidue 14 17 exponent := by
  exact powResidue_add_period vp_vpl_v1_valid_modular_period_prime_filter_008_a46a3aca58_period

theorem vp_vpl_v1_valid_modular_period_prime_filter_008_a46a3aca58_minimal_period : properPeriodWitnesses 14 17 16 = [] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_008_a46a3aca58_classes : residueClasses 14 17 9 16 = [2] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_008_a46a3aca58 : residueClasses 14 17 9 16 = [2] := by
  exact vp_vpl_v1_valid_modular_period_prime_filter_008_a46a3aca58_classes


theorem vp_vpl_v1_valid_modular_period_prime_filter_009_bc3eb6b5ce_period : powResidue 3 5 4 = 1 := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_009_bc3eb6b5ce_periodic (exponent : ℕ) :
    powResidue 3 5 (exponent + 4) = powResidue 3 5 exponent := by
  exact powResidue_add_period vp_vpl_v1_valid_modular_period_prime_filter_009_bc3eb6b5ce_period

theorem vp_vpl_v1_valid_modular_period_prime_filter_009_bc3eb6b5ce_minimal_period : properPeriodWitnesses 3 5 4 = [] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_009_bc3eb6b5ce_classes : residueClasses 3 5 2 4 = [3] := by
  native_decide

theorem vp_vpl_v1_valid_modular_period_prime_filter_009_bc3eb6b5ce : residueClasses 3 5 2 4 = [3] := by
  exact vp_vpl_v1_valid_modular_period_prime_filter_009_bc3eb6b5ce_classes


theorem vp_vpl_v1_valid_finite_double_count_000_2bec1611b7_total : Fintype.card (SubsetTuple 5 3) = 32768 := by
  native_decide

theorem vp_vpl_v1_valid_finite_double_count_000_2bec1611b7_absent : fixedElementAbsentConfigCount 5 3 ⟨0, by norm_num⟩ = 4096 := by
  native_decide

theorem vp_vpl_v1_valid_finite_double_count_000_2bec1611b7_contains : 32768 - 4096 = 28672 := by
  norm_num

theorem vp_vpl_v1_valid_finite_double_count_000_2bec1611b7 : enumeratedUnionIncidences 5 3 = 143360 := by
  native_decide


theorem vp_vpl_v1_valid_finite_double_count_001_8a78eae1b6_total : Fintype.card (SubsetTuple 1 1) = 2 := by
  native_decide

theorem vp_vpl_v1_valid_finite_double_count_001_8a78eae1b6_absent : fixedElementAbsentConfigCount 1 1 ⟨0, by norm_num⟩ = 1 := by
  native_decide

theorem vp_vpl_v1_valid_finite_double_count_001_8a78eae1b6_contains : 2 - 1 = 1 := by
  norm_num

theorem vp_vpl_v1_valid_finite_double_count_001_8a78eae1b6 : enumeratedUnionIncidences 1 1 = 1 := by
  native_decide


theorem vp_vpl_v1_valid_finite_double_count_002_f5e5ae01c3_total : Fintype.card (SubsetTuple 8 2) = 65536 := by
  native_decide

theorem vp_vpl_v1_valid_finite_double_count_002_f5e5ae01c3_absent : fixedElementAbsentConfigCount 8 2 ⟨0, by norm_num⟩ = 16384 := by
  native_decide

theorem vp_vpl_v1_valid_finite_double_count_002_f5e5ae01c3_contains : 65536 - 16384 = 49152 := by
  norm_num

theorem vp_vpl_v1_valid_finite_double_count_002_f5e5ae01c3 : enumeratedUnionIncidences 8 2 = 393216 := by
  native_decide


theorem vp_vpl_v1_valid_finite_double_count_003_75c3aebae6_total : Fintype.card (SubsetTuple 5 3) = 32768 := by
  native_decide

theorem vp_vpl_v1_valid_finite_double_count_003_75c3aebae6_absent : fixedElementAbsentConfigCount 5 3 ⟨0, by norm_num⟩ = 4096 := by
  native_decide

theorem vp_vpl_v1_valid_finite_double_count_003_75c3aebae6_contains : 32768 - 4096 = 28672 := by
  norm_num

theorem vp_vpl_v1_valid_finite_double_count_003_75c3aebae6 : enumeratedUnionIncidences 5 3 = 143360 := by
  native_decide


theorem vp_vpl_v1_valid_finite_double_count_004_05ebd3912f_total : Fintype.card (SubsetTuple 5 1) = 32 := by
  native_decide

theorem vp_vpl_v1_valid_finite_double_count_004_05ebd3912f_absent : fixedElementAbsentConfigCount 5 1 ⟨0, by norm_num⟩ = 16 := by
  native_decide

theorem vp_vpl_v1_valid_finite_double_count_004_05ebd3912f_contains : 32 - 16 = 16 := by
  norm_num

theorem vp_vpl_v1_valid_finite_double_count_004_05ebd3912f : enumeratedUnionIncidences 5 1 = 80 := by
  native_decide


theorem vp_vpl_v1_valid_finite_double_count_005_1ed809ee84_total : Fintype.card (SubsetTuple 3 1) = 8 := by
  native_decide

theorem vp_vpl_v1_valid_finite_double_count_005_1ed809ee84_absent : fixedElementAbsentConfigCount 3 1 ⟨0, by norm_num⟩ = 4 := by
  native_decide

theorem vp_vpl_v1_valid_finite_double_count_005_1ed809ee84_contains : 8 - 4 = 4 := by
  norm_num

theorem vp_vpl_v1_valid_finite_double_count_005_1ed809ee84 : enumeratedUnionIncidences 3 1 = 12 := by
  native_decide


theorem vp_vpl_v1_valid_finite_double_count_006_c56e736bb7_total : Fintype.card (SubsetTuple 1 3) = 8 := by
  native_decide

theorem vp_vpl_v1_valid_finite_double_count_006_c56e736bb7_absent : fixedElementAbsentConfigCount 1 3 ⟨0, by norm_num⟩ = 1 := by
  native_decide

theorem vp_vpl_v1_valid_finite_double_count_006_c56e736bb7_contains : 8 - 1 = 7 := by
  norm_num

theorem vp_vpl_v1_valid_finite_double_count_006_c56e736bb7 : enumeratedUnionIncidences 1 3 = 7 := by
  native_decide


theorem vp_vpl_v1_valid_finite_double_count_007_1af4c39e84_total : Fintype.card (SubsetTuple 4 4) = 65536 := by
  native_decide

theorem vp_vpl_v1_valid_finite_double_count_007_1af4c39e84_absent : fixedElementAbsentConfigCount 4 4 ⟨0, by norm_num⟩ = 4096 := by
  native_decide

theorem vp_vpl_v1_valid_finite_double_count_007_1af4c39e84_contains : 65536 - 4096 = 61440 := by
  norm_num

theorem vp_vpl_v1_valid_finite_double_count_007_1af4c39e84 : enumeratedUnionIncidences 4 4 = 245760 := by
  native_decide


theorem vp_vpl_v1_valid_finite_double_count_008_551441df3a_total : Fintype.card (SubsetTuple 3 2) = 64 := by
  native_decide

theorem vp_vpl_v1_valid_finite_double_count_008_551441df3a_absent : fixedElementAbsentConfigCount 3 2 ⟨0, by norm_num⟩ = 16 := by
  native_decide

theorem vp_vpl_v1_valid_finite_double_count_008_551441df3a_contains : 64 - 16 = 48 := by
  norm_num

theorem vp_vpl_v1_valid_finite_double_count_008_551441df3a : enumeratedUnionIncidences 3 2 = 144 := by
  native_decide


theorem vp_vpl_v1_valid_finite_double_count_009_20851f7010_total : Fintype.card (SubsetTuple 6 1) = 64 := by
  native_decide

theorem vp_vpl_v1_valid_finite_double_count_009_20851f7010_absent : fixedElementAbsentConfigCount 6 1 ⟨0, by norm_num⟩ = 32 := by
  native_decide

theorem vp_vpl_v1_valid_finite_double_count_009_20851f7010_contains : 64 - 32 = 32 := by
  norm_num

theorem vp_vpl_v1_valid_finite_double_count_009_20851f7010 : enumeratedUnionIncidences 6 1 = 192 := by
  native_decide


def vp_vpl_v1_valid_finite_recurrence_period_000_e653ae1c91_step : ℕ × ℕ → ℕ × ℕ := affinePairStep 4 0 1 0 1 0 3

theorem vp_vpl_v1_valid_finite_recurrence_period_000_e653ae1c91_cycle_start : (vp_vpl_v1_valid_finite_recurrence_period_000_e653ae1c91_step^[0]) (1, 1) = (1, 1) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_000_e653ae1c91_repeat : (vp_vpl_v1_valid_finite_recurrence_period_000_e653ae1c91_step^[8]) (1, 1) = (1, 1) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_000_e653ae1c91_no_earlier_repeat : ∀ step ∈ Finset.Icc 1 7, (vp_vpl_v1_valid_finite_recurrence_period_000_e653ae1c91_step^[step]) (1, 1) ≠ (1, 1) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_000_e653ae1c91_reduced_state : (vp_vpl_v1_valid_finite_recurrence_period_000_e653ae1c91_step^[6]) (1, 1) = (2, 2) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_000_e653ae1c91 : (vp_vpl_v1_valid_finite_recurrence_period_000_e653ae1c91_step^[326]) (1, 1) = (2, 2) := by
  have hcycle : (vp_vpl_v1_valid_finite_recurrence_period_000_e653ae1c91_step^[8]) ((vp_vpl_v1_valid_finite_recurrence_period_000_e653ae1c91_step^[0]) (1, 1)) = (vp_vpl_v1_valid_finite_recurrence_period_000_e653ae1c91_step^[0]) (1, 1) := by
    native_decide
  have hreduce := iterate_reduce_after_cycle vp_vpl_v1_valid_finite_recurrence_period_000_e653ae1c91_step (1, 1) (cycleStart := 0) (period := 8) (offset := 326) hcycle
  have hleft : 0 + (326 % 8) = 6 := by norm_num
  have hright : 0 + 326 = 326 := by norm_num
  rw [hleft, hright] at hreduce
  exact hreduce.symm.trans vp_vpl_v1_valid_finite_recurrence_period_000_e653ae1c91_reduced_state


def vp_vpl_v1_valid_finite_recurrence_period_001_ad0a7764c0_step : ℕ × ℕ → ℕ × ℕ := affinePairStep 3 0 1 0 1 0 0

theorem vp_vpl_v1_valid_finite_recurrence_period_001_ad0a7764c0_cycle_start : (vp_vpl_v1_valid_finite_recurrence_period_001_ad0a7764c0_step^[0]) (0, 0) = (0, 0) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_001_ad0a7764c0_repeat : (vp_vpl_v1_valid_finite_recurrence_period_001_ad0a7764c0_step^[1]) (0, 0) = (0, 0) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_001_ad0a7764c0_no_earlier_repeat : ∀ step ∈ Finset.Icc 1 0, (vp_vpl_v1_valid_finite_recurrence_period_001_ad0a7764c0_step^[step]) (0, 0) ≠ (0, 0) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_001_ad0a7764c0_reduced_state : (vp_vpl_v1_valid_finite_recurrence_period_001_ad0a7764c0_step^[0]) (0, 0) = (0, 0) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_001_ad0a7764c0 : (vp_vpl_v1_valid_finite_recurrence_period_001_ad0a7764c0_step^[292]) (0, 0) = (0, 0) := by
  have hcycle : (vp_vpl_v1_valid_finite_recurrence_period_001_ad0a7764c0_step^[1]) ((vp_vpl_v1_valid_finite_recurrence_period_001_ad0a7764c0_step^[0]) (0, 0)) = (vp_vpl_v1_valid_finite_recurrence_period_001_ad0a7764c0_step^[0]) (0, 0) := by
    native_decide
  have hreduce := iterate_reduce_after_cycle vp_vpl_v1_valid_finite_recurrence_period_001_ad0a7764c0_step (0, 0) (cycleStart := 0) (period := 1) (offset := 292) hcycle
  have hleft : 0 + (292 % 1) = 0 := by norm_num
  have hright : 0 + 292 = 292 := by norm_num
  rw [hleft, hright] at hreduce
  exact hreduce.symm.trans vp_vpl_v1_valid_finite_recurrence_period_001_ad0a7764c0_reduced_state


def vp_vpl_v1_valid_finite_recurrence_period_002_ea482c4e2b_step : ℕ × ℕ → ℕ × ℕ := affinePairStep 6 0 1 0 1 4 3

theorem vp_vpl_v1_valid_finite_recurrence_period_002_ea482c4e2b_cycle_start : (vp_vpl_v1_valid_finite_recurrence_period_002_ea482c4e2b_step^[0]) (0, 5) = (0, 5) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_002_ea482c4e2b_repeat : (vp_vpl_v1_valid_finite_recurrence_period_002_ea482c4e2b_step^[8]) (0, 5) = (0, 5) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_002_ea482c4e2b_no_earlier_repeat : ∀ step ∈ Finset.Icc 1 7, (vp_vpl_v1_valid_finite_recurrence_period_002_ea482c4e2b_step^[step]) (0, 5) ≠ (0, 5) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_002_ea482c4e2b_reduced_state : (vp_vpl_v1_valid_finite_recurrence_period_002_ea482c4e2b_step^[1]) (0, 5) = (5, 5) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_002_ea482c4e2b : (vp_vpl_v1_valid_finite_recurrence_period_002_ea482c4e2b_step^[169]) (0, 5) = (5, 5) := by
  have hcycle : (vp_vpl_v1_valid_finite_recurrence_period_002_ea482c4e2b_step^[8]) ((vp_vpl_v1_valid_finite_recurrence_period_002_ea482c4e2b_step^[0]) (0, 5)) = (vp_vpl_v1_valid_finite_recurrence_period_002_ea482c4e2b_step^[0]) (0, 5) := by
    native_decide
  have hreduce := iterate_reduce_after_cycle vp_vpl_v1_valid_finite_recurrence_period_002_ea482c4e2b_step (0, 5) (cycleStart := 0) (period := 8) (offset := 169) hcycle
  have hleft : 0 + (169 % 8) = 1 := by norm_num
  have hright : 0 + 169 = 169 := by norm_num
  rw [hleft, hright] at hreduce
  exact hreduce.symm.trans vp_vpl_v1_valid_finite_recurrence_period_002_ea482c4e2b_reduced_state


def vp_vpl_v1_valid_finite_recurrence_period_003_bf9faa0e24_step : ℕ × ℕ → ℕ × ℕ := affinePairStep 7 0 1 0 1 4 4

theorem vp_vpl_v1_valid_finite_recurrence_period_003_bf9faa0e24_cycle_start : (vp_vpl_v1_valid_finite_recurrence_period_003_bf9faa0e24_step^[0]) (0, 5) = (0, 5) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_003_bf9faa0e24_repeat : (vp_vpl_v1_valid_finite_recurrence_period_003_bf9faa0e24_step^[16]) (0, 5) = (0, 5) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_003_bf9faa0e24_no_earlier_repeat : ∀ step ∈ Finset.Icc 1 15, (vp_vpl_v1_valid_finite_recurrence_period_003_bf9faa0e24_step^[step]) (0, 5) ≠ (0, 5) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_003_bf9faa0e24_reduced_state : (vp_vpl_v1_valid_finite_recurrence_period_003_bf9faa0e24_step^[7]) (0, 5) = (4, 5) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_003_bf9faa0e24 : (vp_vpl_v1_valid_finite_recurrence_period_003_bf9faa0e24_step^[487]) (0, 5) = (4, 5) := by
  have hcycle : (vp_vpl_v1_valid_finite_recurrence_period_003_bf9faa0e24_step^[16]) ((vp_vpl_v1_valid_finite_recurrence_period_003_bf9faa0e24_step^[0]) (0, 5)) = (vp_vpl_v1_valid_finite_recurrence_period_003_bf9faa0e24_step^[0]) (0, 5) := by
    native_decide
  have hreduce := iterate_reduce_after_cycle vp_vpl_v1_valid_finite_recurrence_period_003_bf9faa0e24_step (0, 5) (cycleStart := 0) (period := 16) (offset := 487) hcycle
  have hleft : 0 + (487 % 16) = 7 := by norm_num
  have hright : 0 + 487 = 487 := by norm_num
  rw [hleft, hright] at hreduce
  exact hreduce.symm.trans vp_vpl_v1_valid_finite_recurrence_period_003_bf9faa0e24_reduced_state


def vp_vpl_v1_valid_finite_recurrence_period_004_93d6fab6ec_step : ℕ × ℕ → ℕ × ℕ := affinePairStep 8 0 1 0 1 5 5

theorem vp_vpl_v1_valid_finite_recurrence_period_004_93d6fab6ec_cycle_start : (vp_vpl_v1_valid_finite_recurrence_period_004_93d6fab6ec_step^[0]) (7, 2) = (7, 2) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_004_93d6fab6ec_repeat : (vp_vpl_v1_valid_finite_recurrence_period_004_93d6fab6ec_step^[12]) (7, 2) = (7, 2) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_004_93d6fab6ec_no_earlier_repeat : ∀ step ∈ Finset.Icc 1 11, (vp_vpl_v1_valid_finite_recurrence_period_004_93d6fab6ec_step^[step]) (7, 2) ≠ (7, 2) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_004_93d6fab6ec_reduced_state : (vp_vpl_v1_valid_finite_recurrence_period_004_93d6fab6ec_step^[5]) (7, 2) = (6, 7) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_004_93d6fab6ec : (vp_vpl_v1_valid_finite_recurrence_period_004_93d6fab6ec_step^[185]) (7, 2) = (6, 7) := by
  have hcycle : (vp_vpl_v1_valid_finite_recurrence_period_004_93d6fab6ec_step^[12]) ((vp_vpl_v1_valid_finite_recurrence_period_004_93d6fab6ec_step^[0]) (7, 2)) = (vp_vpl_v1_valid_finite_recurrence_period_004_93d6fab6ec_step^[0]) (7, 2) := by
    native_decide
  have hreduce := iterate_reduce_after_cycle vp_vpl_v1_valid_finite_recurrence_period_004_93d6fab6ec_step (7, 2) (cycleStart := 0) (period := 12) (offset := 185) hcycle
  have hleft : 0 + (185 % 12) = 5 := by norm_num
  have hright : 0 + 185 = 185 := by norm_num
  rw [hleft, hright] at hreduce
  exact hreduce.symm.trans vp_vpl_v1_valid_finite_recurrence_period_004_93d6fab6ec_reduced_state


def vp_vpl_v1_valid_finite_recurrence_period_005_45c6c14d10_step : ℕ × ℕ → ℕ × ℕ := affinePairStep 3 0 1 0 1 2 2

theorem vp_vpl_v1_valid_finite_recurrence_period_005_45c6c14d10_cycle_start : (vp_vpl_v1_valid_finite_recurrence_period_005_45c6c14d10_step^[0]) (0, 0) = (0, 0) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_005_45c6c14d10_repeat : (vp_vpl_v1_valid_finite_recurrence_period_005_45c6c14d10_step^[8]) (0, 0) = (0, 0) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_005_45c6c14d10_no_earlier_repeat : ∀ step ∈ Finset.Icc 1 7, (vp_vpl_v1_valid_finite_recurrence_period_005_45c6c14d10_step^[step]) (0, 0) ≠ (0, 0) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_005_45c6c14d10_reduced_state : (vp_vpl_v1_valid_finite_recurrence_period_005_45c6c14d10_step^[7]) (0, 0) = (1, 0) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_005_45c6c14d10 : (vp_vpl_v1_valid_finite_recurrence_period_005_45c6c14d10_step^[375]) (0, 0) = (1, 0) := by
  have hcycle : (vp_vpl_v1_valid_finite_recurrence_period_005_45c6c14d10_step^[8]) ((vp_vpl_v1_valid_finite_recurrence_period_005_45c6c14d10_step^[0]) (0, 0)) = (vp_vpl_v1_valid_finite_recurrence_period_005_45c6c14d10_step^[0]) (0, 0) := by
    native_decide
  have hreduce := iterate_reduce_after_cycle vp_vpl_v1_valid_finite_recurrence_period_005_45c6c14d10_step (0, 0) (cycleStart := 0) (period := 8) (offset := 375) hcycle
  have hleft : 0 + (375 % 8) = 7 := by norm_num
  have hright : 0 + 375 = 375 := by norm_num
  rw [hleft, hright] at hreduce
  exact hreduce.symm.trans vp_vpl_v1_valid_finite_recurrence_period_005_45c6c14d10_reduced_state


def vp_vpl_v1_valid_finite_recurrence_period_006_db97d3f2e4_step : ℕ × ℕ → ℕ × ℕ := affinePairStep 6 0 1 0 1 5 1

theorem vp_vpl_v1_valid_finite_recurrence_period_006_db97d3f2e4_cycle_start : (vp_vpl_v1_valid_finite_recurrence_period_006_db97d3f2e4_step^[0]) (2, 2) = (2, 2) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_006_db97d3f2e4_repeat : (vp_vpl_v1_valid_finite_recurrence_period_006_db97d3f2e4_step^[24]) (2, 2) = (2, 2) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_006_db97d3f2e4_no_earlier_repeat : ∀ step ∈ Finset.Icc 1 23, (vp_vpl_v1_valid_finite_recurrence_period_006_db97d3f2e4_step^[step]) (2, 2) ≠ (2, 2) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_006_db97d3f2e4_reduced_state : (vp_vpl_v1_valid_finite_recurrence_period_006_db97d3f2e4_step^[17]) (2, 2) = (5, 4) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_006_db97d3f2e4 : (vp_vpl_v1_valid_finite_recurrence_period_006_db97d3f2e4_step^[497]) (2, 2) = (5, 4) := by
  have hcycle : (vp_vpl_v1_valid_finite_recurrence_period_006_db97d3f2e4_step^[24]) ((vp_vpl_v1_valid_finite_recurrence_period_006_db97d3f2e4_step^[0]) (2, 2)) = (vp_vpl_v1_valid_finite_recurrence_period_006_db97d3f2e4_step^[0]) (2, 2) := by
    native_decide
  have hreduce := iterate_reduce_after_cycle vp_vpl_v1_valid_finite_recurrence_period_006_db97d3f2e4_step (2, 2) (cycleStart := 0) (period := 24) (offset := 497) hcycle
  have hleft : 0 + (497 % 24) = 17 := by norm_num
  have hright : 0 + 497 = 497 := by norm_num
  rw [hleft, hright] at hreduce
  exact hreduce.symm.trans vp_vpl_v1_valid_finite_recurrence_period_006_db97d3f2e4_reduced_state


def vp_vpl_v1_valid_finite_recurrence_period_007_cfb23a1f6b_step : ℕ × ℕ → ℕ × ℕ := affinePairStep 6 0 1 0 1 3 3

theorem vp_vpl_v1_valid_finite_recurrence_period_007_cfb23a1f6b_cycle_start : (vp_vpl_v1_valid_finite_recurrence_period_007_cfb23a1f6b_step^[0]) (0, 3) = (0, 3) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_007_cfb23a1f6b_repeat : (vp_vpl_v1_valid_finite_recurrence_period_007_cfb23a1f6b_step^[3]) (0, 3) = (0, 3) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_007_cfb23a1f6b_no_earlier_repeat : ∀ step ∈ Finset.Icc 1 2, (vp_vpl_v1_valid_finite_recurrence_period_007_cfb23a1f6b_step^[step]) (0, 3) ≠ (0, 3) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_007_cfb23a1f6b_reduced_state : (vp_vpl_v1_valid_finite_recurrence_period_007_cfb23a1f6b_step^[1]) (0, 3) = (3, 0) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_007_cfb23a1f6b : (vp_vpl_v1_valid_finite_recurrence_period_007_cfb23a1f6b_step^[151]) (0, 3) = (3, 0) := by
  have hcycle : (vp_vpl_v1_valid_finite_recurrence_period_007_cfb23a1f6b_step^[3]) ((vp_vpl_v1_valid_finite_recurrence_period_007_cfb23a1f6b_step^[0]) (0, 3)) = (vp_vpl_v1_valid_finite_recurrence_period_007_cfb23a1f6b_step^[0]) (0, 3) := by
    native_decide
  have hreduce := iterate_reduce_after_cycle vp_vpl_v1_valid_finite_recurrence_period_007_cfb23a1f6b_step (0, 3) (cycleStart := 0) (period := 3) (offset := 151) hcycle
  have hleft : 0 + (151 % 3) = 1 := by norm_num
  have hright : 0 + 151 = 151 := by norm_num
  rw [hleft, hright] at hreduce
  exact hreduce.symm.trans vp_vpl_v1_valid_finite_recurrence_period_007_cfb23a1f6b_reduced_state


def vp_vpl_v1_valid_finite_recurrence_period_008_a68e6799d9_step : ℕ × ℕ → ℕ × ℕ := affinePairStep 7 0 1 0 1 5 6

theorem vp_vpl_v1_valid_finite_recurrence_period_008_a68e6799d9_cycle_start : (vp_vpl_v1_valid_finite_recurrence_period_008_a68e6799d9_step^[0]) (3, 5) = (3, 5) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_008_a68e6799d9_repeat : (vp_vpl_v1_valid_finite_recurrence_period_008_a68e6799d9_step^[6]) (3, 5) = (3, 5) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_008_a68e6799d9_no_earlier_repeat : ∀ step ∈ Finset.Icc 1 5, (vp_vpl_v1_valid_finite_recurrence_period_008_a68e6799d9_step^[step]) (3, 5) ≠ (3, 5) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_008_a68e6799d9_reduced_state : (vp_vpl_v1_valid_finite_recurrence_period_008_a68e6799d9_step^[5]) (3, 5) = (5, 3) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_008_a68e6799d9 : (vp_vpl_v1_valid_finite_recurrence_period_008_a68e6799d9_step^[167]) (3, 5) = (5, 3) := by
  have hcycle : (vp_vpl_v1_valid_finite_recurrence_period_008_a68e6799d9_step^[6]) ((vp_vpl_v1_valid_finite_recurrence_period_008_a68e6799d9_step^[0]) (3, 5)) = (vp_vpl_v1_valid_finite_recurrence_period_008_a68e6799d9_step^[0]) (3, 5) := by
    native_decide
  have hreduce := iterate_reduce_after_cycle vp_vpl_v1_valid_finite_recurrence_period_008_a68e6799d9_step (3, 5) (cycleStart := 0) (period := 6) (offset := 167) hcycle
  have hleft : 0 + (167 % 6) = 5 := by norm_num
  have hright : 0 + 167 = 167 := by norm_num
  rw [hleft, hright] at hreduce
  exact hreduce.symm.trans vp_vpl_v1_valid_finite_recurrence_period_008_a68e6799d9_reduced_state


def vp_vpl_v1_valid_finite_recurrence_period_009_686c03e966_step : ℕ × ℕ → ℕ × ℕ := affinePairStep 5 0 1 0 1 3 1

theorem vp_vpl_v1_valid_finite_recurrence_period_009_686c03e966_cycle_start : (vp_vpl_v1_valid_finite_recurrence_period_009_686c03e966_step^[0]) (0, 1) = (0, 1) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_009_686c03e966_repeat : (vp_vpl_v1_valid_finite_recurrence_period_009_686c03e966_step^[12]) (0, 1) = (0, 1) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_009_686c03e966_no_earlier_repeat : ∀ step ∈ Finset.Icc 1 11, (vp_vpl_v1_valid_finite_recurrence_period_009_686c03e966_step^[step]) (0, 1) ≠ (0, 1) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_009_686c03e966_reduced_state : (vp_vpl_v1_valid_finite_recurrence_period_009_686c03e966_step^[6]) (0, 1) = (1, 0) := by
  native_decide

theorem vp_vpl_v1_valid_finite_recurrence_period_009_686c03e966 : (vp_vpl_v1_valid_finite_recurrence_period_009_686c03e966_step^[474]) (0, 1) = (1, 0) := by
  have hcycle : (vp_vpl_v1_valid_finite_recurrence_period_009_686c03e966_step^[12]) ((vp_vpl_v1_valid_finite_recurrence_period_009_686c03e966_step^[0]) (0, 1)) = (vp_vpl_v1_valid_finite_recurrence_period_009_686c03e966_step^[0]) (0, 1) := by
    native_decide
  have hreduce := iterate_reduce_after_cycle vp_vpl_v1_valid_finite_recurrence_period_009_686c03e966_step (0, 1) (cycleStart := 0) (period := 12) (offset := 474) hcycle
  have hleft : 0 + (474 % 12) = 6 := by norm_num
  have hright : 0 + 474 = 474 := by norm_num
  rw [hleft, hright] at hreduce
  exact hreduce.symm.trans vp_vpl_v1_valid_finite_recurrence_period_009_686c03e966_reduced_state


end VerifiedPlanCertificates
