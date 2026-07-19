import Mathlib

namespace SmallMathematicianCertificates

theorem cert_dnl_v1_dev_integer_expression_000_a0bc00bbca : ((12 + 18) * 5 - 8 : ℤ) = 142 := by
  norm_num

theorem cert_dnl_v1_dev_integer_expression_001_0553185c36 : ((17 + 9) * 5 - 2 : ℤ) = 128 := by
  norm_num

theorem cert_dnl_v1_dev_integer_expression_002_3de847548c : ((3 + 11) * 13 - 16 : ℤ) = 166 := by
  norm_num

theorem cert_dnl_v1_dev_integer_expression_003_df582ae84c : ((16 + 5) * 17 - 4 : ℤ) = 353 := by
  norm_num

theorem cert_dnl_v1_dev_integer_expression_004_20e1ffe096 : ((7 + 8) * 6 - 3 : ℤ) = 87 := by
  norm_num

theorem cert_dnl_v1_dev_integer_expression_006_5ef9c61f3e : ((19 + 13) * 7 - 19 : ℤ) = 205 := by
  norm_num

theorem cert_dnl_v1_dev_integer_expression_007_2853b04321 : ((7 + 4) * 6 - 10 : ℤ) = 56 := by
  norm_num

theorem cert_dnl_v1_dev_integer_expression_008_d440dddbe4 : ((12 + 9) * 3 - 13 : ℤ) = 50 := by
  norm_num

theorem cert_dnl_v1_dev_integer_expression_009_7394abe8c1 : ((12 + 17) * 17 - 17 : ℤ) = 476 := by
  norm_num

theorem cert_dnl_v1_dev_integer_expression_010_0e5916b3da : ((10 + 11) * 18 - 4 : ℤ) = 374 := by
  norm_num

theorem cert_dnl_v1_dev_integer_expression_011_3f09472b67 : ((4 + 11) * 11 - 9 : ℤ) = 156 := by
  norm_num

theorem cert_dnl_v1_dev_modular_inverse_002_516924afe7 : (4 * 4) % 15 = 1 ∧ 4 < 15 := by
  norm_num

theorem cert_dnl_v1_dev_quadratic_integer_roots_006_d590798eba : ((6 : ℤ)^2 + (-13) * 6 + 42 = 0) ∧ ((7 : ℤ)^2 + (-13) * 7 + 42 = 0) ∧ (∀ x : ℤ, x^2 + (-13) * x + 42 = 0 → x = 6 ∨ x = 7) := by
  constructor
  · norm_num
  constructor
  · norm_num
  · intro x hx
    have hprod : (x - 6) * (x - 7) = 0 := by nlinarith
    rcases mul_eq_zero.mp hprod with h | h
    · left; linarith
    · right; linarith

theorem cert_dnl_v1_dev_quadratic_integer_roots_007_1005c87732 : (((-7) : ℤ)^2 + 0 * (-7) + (-49) = 0) ∧ ((7 : ℤ)^2 + 0 * 7 + (-49) = 0) ∧ (∀ x : ℤ, x^2 + 0 * x + (-49) = 0 → x = (-7) ∨ x = 7) := by
  constructor
  · norm_num
  constructor
  · norm_num
  · intro x hx
    have hprod : (x - (-7)) * (x - 7) = 0 := by nlinarith
    rcases mul_eq_zero.mp hprod with h | h
    · left; linarith
    · right; linarith

theorem cert_dnl_v1_dev_quadratic_integer_roots_008_8187ca763f : ((4 : ℤ)^2 + (-13) * 4 + 36 = 0) ∧ ((9 : ℤ)^2 + (-13) * 9 + 36 = 0) ∧ (∀ x : ℤ, x^2 + (-13) * x + 36 = 0 → x = 4 ∨ x = 9) := by
  constructor
  · norm_num
  constructor
  · norm_num
  · intro x hx
    have hprod : (x - 4) * (x - 9) = 0 := by nlinarith
    rcases mul_eq_zero.mp hprod with h | h
    · left; linarith
    · right; linarith

theorem cert_dnl_v1_dev_quadratic_integer_roots_009_eea91191e0 : (((-1) : ℤ)^2 + (-7) * (-1) + (-8) = 0) ∧ ((8 : ℤ)^2 + (-7) * 8 + (-8) = 0) ∧ (∀ x : ℤ, x^2 + (-7) * x + (-8) = 0 → x = (-1) ∨ x = 8) := by
  constructor
  · norm_num
  constructor
  · norm_num
  · intro x hx
    have hprod : (x - (-1)) * (x - 8) = 0 := by nlinarith
    rcases mul_eq_zero.mp hprod with h | h
    · left; linarith
    · right; linarith

theorem cert_dnl_v1_dev_quadratic_integer_roots_010_502bc44a79 : ((5 : ℤ)^2 + (-14) * 5 + 45 = 0) ∧ ((9 : ℤ)^2 + (-14) * 9 + 45 = 0) ∧ (∀ x : ℤ, x^2 + (-14) * x + 45 = 0 → x = 5 ∨ x = 9) := by
  constructor
  · norm_num
  constructor
  · norm_num
  · intro x hx
    have hprod : (x - 5) * (x - 9) = 0 := by nlinarith
    rcases mul_eq_zero.mp hprod with h | h
    · left; linarith
    · right; linarith

end SmallMathematicianCertificates
