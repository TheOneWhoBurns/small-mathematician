import VerifiedPlanHelpers

namespace VerifiedPlanCertificates

open Polynomial VerifiedPlanHelpers

theorem vp_vpl_v1_near_diophantine_solvability_001_e0a8b7d314_gcd : Nat.gcd (318 : ℤ).natAbs (72 : ℤ).natAbs = 6 := by
  norm_num [Int.natAbs]

theorem vp_vpl_v1_near_diophantine_solvability_001_e0a8b7d314 : ¬ (∃ x y : ℤ, 318 * x + 72 * y = (-15)) := by
  apply no_diophantine_solution_of_common_dvd (g := 6)
  · norm_num
  · norm_num
  · norm_num


theorem vp_vpl_v1_near_diophantine_solvability_012_df0e02beb4_gcd : Nat.gcd (264 : ℤ).natAbs (1740 : ℤ).natAbs = 12 := by
  norm_num [Int.natAbs]

theorem vp_vpl_v1_near_diophantine_solvability_012_df0e02beb4 : ¬ (∃ x y : ℤ, 264 * x + 1740 * y = 78) := by
  apply no_diophantine_solution_of_common_dvd (g := 12)
  · norm_num
  · norm_num
  · norm_num


end VerifiedPlanCertificates
