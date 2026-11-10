module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

namespace Erdos970

section

namespace ErdosDivisorBounds

theorem local_power_bound {eps : ℝ} (heps : 0 < eps) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ p : ℕ, 2 ≤ p → ∀ k : ℕ,
      (k : ℝ) + 1 ≤ B * ((p : ℝ)^eps)^k := by
  let a : ℝ := (2 : ℝ)^eps - 1
  have ha : 0 < a := sub_pos.mpr (Real.one_lt_rpow (by norm_num) heps)
  let B : ℝ := 1 + a⁻¹
  have hB : 1 ≤ B := by
    dsimp [B]
    exact le_add_of_nonneg_right (inv_nonneg.mpr ha.le)
  have hBa : B*a = a+1 := by dsimp [B]; field_simp
  refine ⟨B,hB,?_⟩
  intro p hp k
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlin : (k : ℝ)+1 ≤ B*(1+(k : ℝ)*a) := by
    have hm := mul_le_mul_of_nonneg_right (show 1 ≤ B*a by rw [hBa]; linarith) hk
    nlinarith
  have hbern := one_add_mul_le_pow (a:=a) (by linarith : -2 ≤ a) k
  have heq : 1+a = (2 : ℝ)^eps := by dsimp [a]; ring
  have hpp : (2 : ℝ)^eps ≤ (p : ℝ)^eps :=
    Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp) heps.le
  calc
    _ ≤ B*(1+(k : ℝ)*a) := hlin
    _ ≤ B*(1+a)^k := mul_le_mul_of_nonneg_left hbern (by linarith)
    _ = B*((2 : ℝ)^eps)^k := by rw [heq]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hpp k) (by linarith)

theorem large_prime_power_bound {eps : ℝ} (heps : 0 < eps) :
    ∃ P : ℕ, ∀ p : ℕ, P ≤ p → ∀ k : ℕ,
      (k : ℝ)+1 ≤ ((p : ℝ)^eps)^k := by
  obtain ⟨P,hP⟩ := exists_nat_ge ((2 : ℝ)^(1/eps))
  refine ⟨P,?_⟩
  intro p hp k
  have hpp : (2 : ℝ)^(1/eps) ≤ (p : ℝ) := hP.trans (by exact_mod_cast hp)
  have hr := Real.rpow_le_rpow (by positivity : 0 ≤ (2 : ℝ)^(1/eps)) hpp heps.le
  have he : ((2 : ℝ)^(1/eps))^eps = 2 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
    norm_num
  rw [he] at hr
  have hb := one_add_mul_le_pow (a:=(1 : ℝ)) (by norm_num) k
  have hlin : (k : ℝ)+1 ≤ (2 : ℝ)^k := by simpa only [mul_one, one_add_one_eq_two, add_comm] using hb
  exact hlin.trans (pow_le_pow_left₀ (by norm_num) hr k)

end ErdosDivisorBounds

end

end Erdos970

end OAI
