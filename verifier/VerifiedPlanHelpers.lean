import Mathlib

/-!
Small, fixed lemmas used by the verified-plan certificate emitter.

The generated certificates supply every numeral appearing in these lemmas from
the model's parsed natural-language plan.  This file deliberately contains no
benchmark answers or row-specific facts.
-/

namespace VerifiedPlanHelpers

open Polynomial

/-! ## Polynomial value obstruction -/

theorem polynomial_value_difference_dvd (P : Polynomial ℤ) (u v : ℤ) :
    (v - u) ∣ (P.eval v - P.eval u) := by
  exact Polynomial.sub_dvd_eval_sub v u P

theorem no_polynomial_with_values_of_not_dvd
    {u v A B : ℤ} (h : ¬ (v - u) ∣ (B - A)) :
    ¬ ∃ P : Polynomial ℤ, P.eval u = A ∧ P.eval v = B := by
  rintro ⟨P, hu, hv⟩
  apply h
  simpa [hu, hv] using polynomial_value_difference_dvd P u v

noncomputable def linearPolynomialWitness (q u A : ℤ) : Polynomial ℤ :=
  C q * (X - C u) + C A

@[simp] theorem linearPolynomialWitness_eval (q u A x : ℤ) :
    (linearPolynomialWitness q u A).eval x = q * (x - u) + A := by
  simp [linearPolynomialWitness]

/-! ## Linear Diophantine equations -/

theorem no_diophantine_solution_of_common_dvd
    {a b c g : ℤ} (ha : g ∣ a) (hb : g ∣ b) (hc : ¬ g ∣ c) :
    ¬ ∃ x y : ℤ, a * x + b * y = c := by
  rintro ⟨x, y, hxy⟩
  apply hc
  rw [← hxy]
  exact (dvd_mul_of_dvd_left ha x).add (dvd_mul_of_dvd_left hb y)

/-! ## Bounded modular prime filters -/

def powResidue (base modulus exponent : ℕ) : ℕ :=
  base ^ exponent % modulus

theorem powResidue_add_period
    {base modulus period exponent : ℕ}
    (hperiod : powResidue base modulus period = 1) :
    powResidue base modulus (exponent + period) = powResidue base modulus exponent := by
  simp only [powResidue] at hperiod ⊢
  rw [pow_add, Nat.mul_mod, hperiod, Nat.mul_one, Nat.mod_mod]

def residueClasses (base modulus target period : ℕ) : List ℕ :=
  (List.range period).filter fun exponent => powResidue base modulus exponent = target

def properPeriodWitnesses (base modulus period : ℕ) : List ℕ :=
  (List.range period).filter fun exponent =>
    0 < exponent ∧ powResidue base modulus exponent = 1

def primesInClosedRange (lo hi : ℕ) : List ℕ :=
  (List.range (hi + 1)).filter fun n => lo ≤ n ∧ Nat.Prime n

def validPrimeExponents
    (base modulus target lo hi : ℕ) : List ℕ :=
  (primesInClosedRange lo hi).filter fun p => powResidue base modulus p = target

/-! ## Exact finite double counts -/

/-- An ordered tuple of subsets, represented by its element/subset incidence bits. -/
abbrev SubsetTuple (universeSize tupleLength : ℕ) :=
  Fin universeSize → Fin tupleLength → Bool

def fixedElementAbsentConfigCount
    (universeSize tupleLength : ℕ) (element : Fin universeSize) : ℕ :=
  (Finset.univ.filter fun config : SubsetTuple universeSize tupleLength =>
    ∀ subsetIndex, config element subsetIndex = false).card

def configUnionCard
    {universeSize tupleLength : ℕ}
    (config : SubsetTuple universeSize tupleLength) : ℕ :=
  (Finset.univ.filter fun element =>
    ∃ subsetIndex, config element subsetIndex = true).card

/-- The literal finite sum of union cardinalities over every ordered subset tuple. -/
def enumeratedUnionIncidences (universeSize tupleLength : ℕ) : ℕ :=
  ∑ config : SubsetTuple universeSize tupleLength, configUnionCard config

def configWeightedUnion
    {universeSize tupleLength : ℕ}
    (classOneSize classOneWeight classTwoWeight : ℕ)
    (config : SubsetTuple universeSize tupleLength) : ℕ :=
  ∑ element ∈ Finset.univ.filter (fun element =>
      ∃ subsetIndex, config element subsetIndex = true),
    if element.val < classOneSize then classOneWeight else classTwoWeight

def enumeratedWeightedUnionIncidences
    (universeSize tupleLength classOneSize classOneWeight classTwoWeight : ℕ) : ℕ :=
  ∑ config : SubsetTuple universeSize tupleLength,
    configWeightedUnion classOneSize classOneWeight classTwoWeight config

/-! ## Finite deterministic recurrences -/

def affinePairStep
    (modulus ax ay ac bx bY bc : ℕ) (state : ℕ × ℕ) : ℕ × ℕ :=
  ((ax * state.1 + ay * state.2 + ac) % modulus,
   (bx * state.1 + bY * state.2 + bc) % modulus)

theorem iterate_reduce_after_cycle
    {State : Type*} (step : State → State) (start : State)
    {cycleStart period offset : ℕ}
    (hcycle : (step^[period]) ((step^[cycleStart]) start) =
      (step^[cycleStart]) start) :
    (step^[cycleStart + offset % period]) start =
      (step^[cycleStart + offset]) start := by
  have hp : Function.IsPeriodicPt step period ((step^[cycleStart]) start) := hcycle
  have hreduce := hp.iterate_mod_apply offset
  rw [Nat.add_comm cycleStart (offset % period), Nat.add_comm cycleStart offset]
  simpa [Function.iterate_add_apply] using hreduce

end VerifiedPlanHelpers
