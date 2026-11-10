module

public import ArtinMatthews.SpectralTrueWidthKloosterman
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The determinant removes one full modulus from the true-width matrix count. -/
noncomputable section
open Matrix
open scoped MatrixGroups

namespace ArtinMatthews

def gamma0TrueWidthReducedMatrixLift (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) : gamma0TrueWidthReducedMatrix N r s c →
      ZMod (gamma0CuspTrueWidth N s * c) × ZMod (gamma0CuspTrueWidth N r) :=
  fun R => ((R.val 0 0 : ZMod (gamma0CuspTrueWidth N s * c)),
    ((R.val 1 1 / (c : ℤ) : ℤ) : ZMod (gamma0CuspTrueWidth N r)))

private theorem specialLinear_diagonal_difference_dvd {c : ℤ}
    (M R : SL(2, ℤ)) (hM : M 1 0 = c) (hR : R 1 0 = c)
    (hA : M 0 0 = R 0 0) : c ∣ M 1 1 - R 1 1 := by
  have hm := M.prop
  have hr := R.prop
  rw [Matrix.det_fin_two, hM, hA] at hm
  rw [Matrix.det_fin_two, hR] at hr
  refine ⟨M 0 1 * R 1 1 - R 0 1 * M 1 1, ?_⟩
  linear_combination R 1 1 * hm - M 1 1 * hr

theorem gamma0TrueWidthReducedMatrix_lift_injective (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] :
    Function.Injective (gamma0TrueWidthReducedMatrixLift N r s c) := by
  intro M R h
  have hc : 0 < (c : ℤ) := by exact_mod_cast NeZero.pos c
  have hA := (ZMod.intCast_eq_intCast_iff _ _ _).mp (congrArg Prod.fst h)
  have hA' : M.val 0 0 = R.val 0 0 := by
    change M.val 0 0 % ((gamma0CuspTrueWidth N s * c : ℕ) : ℤ) =
      R.val 0 0 % ((gamma0CuspTrueWidth N s * c : ℕ) : ℤ) at hA
    push_cast at hA
    simpa only [Int.emod_eq_of_lt M.property.2.2.1 M.property.2.2.2.1,
      Int.emod_eq_of_lt R.property.2.2.1 R.property.2.2.2.1] using hA
  have hDdvd : (c : ℤ) ∣ M.val 1 1 - R.val 1 1 :=
    specialLinear_diagonal_difference_dvd M.val R.val M.property.2.1 R.property.2.1 hA'
  have hrem : M.val 1 1 % (c : ℤ) = R.val 1 1 % (c : ℤ) :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hDdvd)
  have hMquot : 0 ≤ M.val 1 1 / (c : ℤ) ∧
      M.val 1 1 / (c : ℤ) < (gamma0CuspTrueWidth N r : ℤ) :=
    ⟨Int.ediv_nonneg M.property.2.2.2.2.1 hc.le,
      Int.ediv_lt_of_lt_mul hc M.property.2.2.2.2.2⟩
  have hRquot : 0 ≤ R.val 1 1 / (c : ℤ) ∧
      R.val 1 1 / (c : ℤ) < (gamma0CuspTrueWidth N r : ℤ) :=
    ⟨Int.ediv_nonneg R.property.2.2.2.2.1 hc.le,
      Int.ediv_lt_of_lt_mul hc R.property.2.2.2.2.2⟩
  have hquot := (ZMod.intCast_eq_intCast_iff _ _ _).mp (congrArg Prod.snd h)
  have hquot' : M.val 1 1 / (c : ℤ) = R.val 1 1 / (c : ℤ) := by
    change (M.val 1 1 / (c : ℤ)) % (gamma0CuspTrueWidth N r : ℤ) =
      (R.val 1 1 / (c : ℤ)) % (gamma0CuspTrueWidth N r : ℤ) at hquot
    simpa only [Int.emod_eq_of_lt hMquot.1 hMquot.2,
      Int.emod_eq_of_lt hRquot.1 hRquot.2] using hquot
  have hD' : M.val 1 1 = R.val 1 1 := by
    calc
      _ = M.val 1 1 % (c : ℤ) + M.val 1 1 / (c : ℤ) * (c : ℤ) :=
        (Int.emod_add_ediv_mul _ _).symm
      _ = R.val 1 1 % (c : ℤ) + R.val 1 1 / (c : ℤ) * (c : ℤ) := by rw [hrem, hquot']
      _ = _ := Int.emod_add_ediv_mul _ _
  apply Subtype.ext
  exact specialLinear_eq_of_diagonal_lower hc.ne' M.val R.val M.property.2.1 R.property.2.1 hA' hD'

theorem gamma0TrueWidthReducedMatrix_card_le (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] :
    Fintype.card (gamma0TrueWidthReducedMatrix N r s c) ≤
      gamma0CuspTrueWidth N r * gamma0CuspTrueWidth N s * c := by
  let : NeZero (gamma0CuspTrueWidth N s * c) :=
    ⟨Nat.mul_ne_zero (gamma0CuspTrueWidth_pos N s).ne' (NeZero.ne c)⟩
  let : NeZero (gamma0CuspTrueWidth N r) := ⟨(gamma0CuspTrueWidth_pos N r).ne'⟩
  have hcard := Fintype.card_le_of_injective (gamma0TrueWidthReducedMatrixLift N r s c)
    (gamma0TrueWidthReducedMatrix_lift_injective N r s c)
  simpa only [Fintype.card_prod, ZMod.card, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcard

theorem gamma0TrueWidthKloostermanSum_linear_bound (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] (m n : ℤ) :
    ‖gamma0TrueWidthKloostermanSum N r s c m n‖ ≤
      (gamma0CuspTrueWidth N r : ℝ) * gamma0CuspTrueWidth N s * c := by
  refine (gamma0TrueWidthKloostermanSum_trivial_bound N r s c m n).trans ?_
  exact_mod_cast gamma0TrueWidthReducedMatrix_card_le N r s c

end ArtinMatthews
