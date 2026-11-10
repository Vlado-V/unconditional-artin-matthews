module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-! The original admissible modulus family and an explicit plateau subset. -/

noncomputable section
namespace ArtinMatthews

def circleModuli (F r L : ℕ) : Finset ℕ :=
  (Finset.Icc (3 * L) (6 * L)).filter (fun q => F ∣ q ∧ q.Coprime r)

def circleBlockLength (F r L : ℕ) : ℕ := L / (2 * (F * r))

def circleResidueBlocks (F r L : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (circleBlockLength F r L)).product
    ((Finset.range r).filter (fun a => r.Coprime a))

def circleBlockModulus (F r L : ℕ) (p : ℕ × ℕ) : ℕ :=
  F * (r * (4 * L / (F * r) + 1 + p.1) + p.2)

def circlePlateauModuli (F r L : ℕ) : Finset ℕ :=
  (circleResidueBlocks F r L).image (circleBlockModulus F r L)

end ArtinMatthews
