module

public import ArtinMatthews.KloostermanWeakBound
public import OAI.NumberTheory.JointDickman.Arithmetic.RamanujanDivisorFormula
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Analysis.CStarAlgebra.Classes


set_option backward.privateInPublic true
@[expose] public section

/-!
# The zero-frequency Kloosterman diagonal

The ordinary zero-frequency Kloosterman sum is the genuine Ramanujan sum.
Its exact Möbius divisor expansion retains the integer-frequency divisibility
conditions needed when the modulus is averaged.
-/

namespace ArtinMatthews

open scoped BigOperators ArithmeticFunction.Moebius

set_option backward.isDefEq.respectTransparency false in
/-- The Kloosterman sum with its inverse frequency zero is the Ramanujan sum. -/
theorem unitKloostermanSum_zero_eq_ramanujanSum (q : ℕ) [NeZero q] (b : ZMod q) :
    unitKloostermanSum q b 0 = OAI.JointDickman.ramanujanSum q b := by
  classical
  unfold unitKloostermanSum doubleCharacterSum OAI.JointDickman.ramanujanSum
  apply Finset.sum_congr (by ext u; simp)
  intro u _hu
  rw [zmodAddEquiv_apply_eq_stdAddChar, zmodAddEquiv_apply_eq_stdAddChar]
  simp

/-- The ordinary additive-character convention used in the double Voronoi
identity has precisely the same zero-frequency diagonal. -/
theorem ordinaryKloosterman_zero_eq_ramanujanSum (q : ℕ) [NeZero q] (b : ZMod q) :
    OAI.Erdos970.ErdosKloosterman.sum ZMod.stdAddChar b 0 =
      OAI.JointDickman.ramanujanSum q b := by
  classical
  unfold OAI.Erdos970.ErdosKloosterman.sum OAI.JointDickman.ramanujanSum
  simp only [zero_mul, add_zero]
  exact Finset.sum_congr (by ext u; simp) (fun _u _hu => rfl)

theorem ordinaryKloosterman_zero_eq_unit (q : ℕ) [NeZero q] (b : ZMod q) :
    OAI.Erdos970.ErdosKloosterman.sum ZMod.stdAddChar b 0 =
      unitKloostermanSum q b 0 := by
  rw [ordinaryKloosterman_zero_eq_ramanujanSum, unitKloostermanSum_zero_eq_ramanujanSum]

/-- Divisibility of a residue representative by a divisor of the modulus is
exactly divisibility of the original integer frequency. -/
theorem kloosterman_residue_dvd_iff {q d : ℕ} [NeZero q] (hd : d ∣ q) (b : ℤ) :
    d ∣ (b : ZMod q).val ↔ (d : ℤ) ∣ b := by
  have hq : (q : ℤ) ∣ b - ((b : ZMod q).val : ℤ) := by
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ q).mp
    simp
  have hdiff : (d : ℤ) ∣ b - ((b : ZMod q).val : ℤ) :=
    dvd_trans (by exact_mod_cast hd) hq
  rw [← Int.natCast_dvd_natCast]
  constructor
  · intro hv
    convert dvd_add hdiff hv using 1; ring
  · intro hb
    convert dvd_sub hb hdiff using 1; ring

/-- Exact integer-frequency expansion, including negative frequencies. -/
theorem unitKloostermanSum_zero_divisor_formula (q : ℕ) [NeZero q] (b : ℤ) :
    unitKloostermanSum q (b : ZMod q) 0 =
      ∑ d ∈ q.divisors, (μ (q / d) : ℂ) *
        (if (d : ℤ) ∣ b then (d : ℂ) else 0) := by
  classical
  rw [unitKloostermanSum_zero_eq_ramanujanSum]
  have h := OAI.JointDickman.ramanujanSum_divisor_formula q (b : ZMod q).val
  rw [ZMod.natCast_zmod_val] at h
  rw [Nat.sum_divisorsAntidiagonal' (fun c d : ℕ => (μ c : ℂ) *
    (if d ∣ (b : ZMod q).val then (d : ℂ) else 0))] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [kloosterman_residue_dvd_iff (Nat.dvd_of_mem_divisors hd)]

/-- The divisor-supported diagonal envelope, before any averaging in `q`. -/
theorem unitKloostermanSum_zero_norm_le_divisor_sum (q : ℕ) [NeZero q] (b : ℤ) :
    ‖unitKloostermanSum q (b : ZMod q) 0‖ ≤
      ∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℤ) ∣ b), (d : ℝ) := by
  classical
  rw [unitKloostermanSum_zero_divisor_formula, Finset.sum_filter]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro d _hd
  by_cases hdb : (d : ℤ) ∣ b
  · simp only [ite_eq_left hdb, norm_mul, Complex.norm_natCast]
    have hm : ‖(μ (q / d) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q / d))
    exact mul_le_of_le_one_left (Nat.cast_nonneg d) hm
  · simp only [ite_eq_right hdb, mul_zero, norm_zero, le_refl]

/-- The supported divisors are exactly the divisors of the frequency gcd. -/
theorem kloosterman_diagonal_divisor_filter (q : ℕ) [NeZero q] (b : ℤ) :
    q.divisors.filter (fun d : ℕ => (d : ℤ) ∣ b) = (Nat.gcd q b.natAbs).divisors := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Int.natCast_dvd, Nat.dvd_gcd_iff]
  have hq : q ≠ 0 := NeZero.ne q
  have hg : Nat.gcd q b.natAbs ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _ (NeZero.pos q))
  tauto

/-- The same bound in the usual gcd-divisor form. -/
theorem unitKloostermanSum_zero_norm_le_gcd_divisors (q : ℕ) [NeZero q] (b : ℤ) :
    ‖unitKloostermanSum q (b : ZMod q) 0‖ ≤
      ∑ d ∈ (Nat.gcd q b.natAbs).divisors, (d : ℝ) := by
  simpa only [kloosterman_diagonal_divisor_filter] using
    unitKloostermanSum_zero_norm_le_divisor_sum q b

/-- A convenient coarse bound that still depends only on the frequency gcd. -/
theorem unitKloostermanSum_zero_norm_le_gcd_mul_divisorCard
    (q : ℕ) [NeZero q] (b : ℤ) :
    ‖unitKloostermanSum q (b : ZMod q) 0‖ ≤
      (Nat.gcd q b.natAbs : ℝ) * ((Nat.gcd q b.natAbs).divisors.card : ℝ) := by
  refine (unitKloostermanSum_zero_norm_le_gcd_divisors q b).trans ?_
  calc
    _ ≤ ∑ _d ∈ (Nat.gcd q b.natAbs).divisors, (Nat.gcd q b.natAbs : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact_mod_cast Nat.le_of_dvd
        (Nat.gcd_pos_of_pos_left _ (NeZero.pos q)) (Nat.dvd_of_mem_divisors hd)
    _ = _ := by simp [mul_comm]

/-- For a nonzero frequency the envelope is uniformly bounded by a sum over
its own divisors, independently of the modulus. -/
theorem unitKloostermanSum_zero_norm_le_frequency_divisors
    (q : ℕ) [NeZero q] {b : ℤ} (hb : b ≠ 0) :
    ‖unitKloostermanSum q (b : ZMod q) 0‖ ≤
      ∑ d ∈ b.natAbs.divisors, (d : ℝ) := by
  refine (unitKloostermanSum_zero_norm_le_gcd_divisors q b).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Nat.divisors_subset_of_dvd (Int.natAbs_ne_zero.mpr hb) (Nat.gcd_dvd_right q b.natAbs))
    (by intro d _hd _h; positivity)

/-- The exact formula in the ordinary sum convention of the dual identity. -/
theorem ordinaryKloosterman_zero_divisor_formula (q : ℕ) [NeZero q] (b : ℤ) :
    OAI.Erdos970.ErdosKloosterman.sum ZMod.stdAddChar (b : ZMod q) 0 =
      ∑ d ∈ q.divisors, (μ (q / d) : ℂ) *
        (if (d : ℤ) ∣ b then (d : ℂ) else 0) := by
  rw [ordinaryKloosterman_zero_eq_unit, unitKloostermanSum_zero_divisor_formula]

/-- The same exact formula for the existing integer-frequency standard sum. -/
theorem standardKloosterman_zero_divisor_formula (q : ℕ) [NeZero q] (b : ℤ) :
    OAI.Erdos970.ErdosKloosterman.standardSum q b 0 =
      ∑ d ∈ q.divisors, (μ (q / d) : ℂ) *
        (if (d : ℤ) ∣ b then (d : ℂ) else 0) := by
  simpa only [OAI.Erdos970.ErdosKloosterman.standardSum, Int.cast_zero] using
    ordinaryKloosterman_zero_divisor_formula q b

/-- An ordinary zero-frequency Kloosterman sum has the exact divisor-supported
norm envelope, with no restriction that the integer frequency be positive. -/
theorem ordinaryKloosterman_zero_norm_le_divisor_sum (q : ℕ) [NeZero q] (b : ℤ) :
    ‖OAI.Erdos970.ErdosKloosterman.sum ZMod.stdAddChar (b : ZMod q) 0‖ ≤
      ∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℤ) ∣ b), (d : ℝ) := by
  rw [ordinaryKloosterman_zero_eq_unit]
  exact unitKloostermanSum_zero_norm_le_divisor_sum q b

/-- In particular, the nonzero difference `m₃-m₄` has a modulus-independent
finite divisor envelope. -/
theorem ordinaryKloosterman_zero_norm_le_frequency_divisors
    (q : ℕ) [NeZero q] {b : ℤ} (hb : b ≠ 0) :
    ‖OAI.Erdos970.ErdosKloosterman.sum ZMod.stdAddChar (b : ZMod q) 0‖ ≤
      ∑ d ∈ b.natAbs.divisors, (d : ℝ) := by
  rw [ordinaryKloosterman_zero_eq_unit]
  exact unitKloostermanSum_zero_norm_le_frequency_divisors q hb

end ArtinMatthews
