module

public import ArtinMatthews.ShiftedDoubleVoronoiFubini
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Compact positive source weights give literal finite support of the
coefficient-pair sequence; no truncation error occurs on the source side. -/

noncomputable section
open Complex UpperHalfPlane Set
namespace ArtinMatthews

theorem cuspSourcePair_eq_zero_of_not_box {F : Type*} [FunLike F ℍ ℂ]
    (f : F) (H1 H2 : ℝ → ℂ) (K1 K2 : ℕ)
    (u1 v1 u2 v2 : ℝ) (hu1 : 0<u1) (hu2 : 0<u2)
    (hv1 : v1≤K1) (hv2 : v2≤K2)
    (hw1 : Function.support H1 ⊆ Icc u1 v1) (hw2 : Function.support H2 ⊆ Icc u2 v2)
    (k : ℕ×ℕ) (hk : k∉(Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2)) :
    cuspSourcePair f H1 H2 k=0 := by
  by_contra h
  have h1 : H1 k.1≠0 := by intro he; apply h; simp [cuspSourcePair,he]
  have h2 : H2 k.2≠0 := by intro he; apply h; simp [cuspSourcePair,he]
  have hb1 := hw1 h1
  have hb2 := hw2 h2
  have hlo1 : 0<k.1 := by exact_mod_cast (hu1.trans_le hb1.1)
  have hlo2 : 0<k.2 := by exact_mod_cast (hu2.trans_le hb2.1)
  have hhi1 : k.1≤K1 := by exact_mod_cast (hb1.2.trans hv1)
  have hhi2 : k.2≤K2 := by exact_mod_cast (hb2.2.trans hv2)
  apply hk
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hlo1,hhi1⟩,
    Finset.mem_Icc.mpr ⟨hlo2,hhi2⟩⟩

end ArtinMatthews
