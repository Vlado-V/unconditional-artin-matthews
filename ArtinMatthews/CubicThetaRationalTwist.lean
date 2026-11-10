module

public import ArtinMatthews.CubicThetaWeightedCuspLimit
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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


set_option backward.privateInPublic true
@[expose] public section

/-! Rational translation of the actual periodic Eisenstein theta series. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators
open Complex UpperHalfPlane
open OAI OAI.SevenEighths

/-- The integral Eisenstein norm polynomial. -/
def eisensteinIntegerNorm (n : ℤ × ℤ) : ℤ := n.1 ^ 2 - n.1 * n.2 + n.2 ^ 2

/-- The norm changes by a multiple of the coordinate period on every residue class. -/
theorem eisensteinIntegerNorm_residue_dvd (N : ℕ) [NeZero N] (n : ℤ × ℤ) :
    (N : ℤ) ∣ eisensteinIntegerNorm n -
      eisensteinIntegerNorm (((HeckeTheta.residueEquiv N n).1.1 : ℤ),
        ((HeckeTheta.residueEquiv N n).1.2 : ℤ)) := by
  obtain ⟨p, rfl⟩ := (HeckeTheta.residueEquiv N).symm.surjective n
  simp only [Equiv.apply_symm_apply]
  refine ⟨(N : ℤ) * (p.2.1 ^ 2 - p.2.1 * p.2.2 + p.2.2 ^ 2) +
    2 * (p.1.1 : ℤ) * p.2.1 - (p.1.1 : ℤ) * p.2.2 -
      (p.1.2 : ℤ) * p.2.1 + 2 * (p.1.2 : ℤ) * p.2.2, ?_⟩
  change eisensteinIntegerNorm
      (p.2.1 * (N : ℤ) + p.1.1, p.2.2 * (N : ℤ) + p.1.2) -
    eisensteinIntegerNorm (p.1.1, p.1.2) = _
  unfold eisensteinIntegerNorm
  ring

/-- The additive phase produced by translation by `a/N`. -/
def eisensteinRationalPhase (a : ℤ) (N : ℕ) (n : ℤ × ℤ) : ℂ :=
  Complex.exp ((a : ℂ) / N * (2 * (Real.pi : ℂ) * Complex.I) *
    (eisensteinIntegerNorm n : ℂ))

theorem eisensteinRationalPhase_residue (a : ℤ) (N : ℕ) [NeZero N]
    (n : ℤ × ℤ) :
    eisensteinRationalPhase a N n = eisensteinRationalPhase a N
      (((HeckeTheta.residueEquiv N n).1.1 : ℤ),
        ((HeckeTheta.residueEquiv N n).1.2 : ℤ)) := by
  obtain ⟨k, hk⟩ := eisensteinIntegerNorm_residue_dvd N n
  unfold eisensteinRationalPhase
  apply Complex.exp_eq_exp_iff_exp_sub_eq_one.mpr
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨a * k, ?_⟩
  have hkc := congrArg (fun z : ℤ => (z : ℂ)) hk
  push_cast at hkc ⊢
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  calc
    _ = (a : ℂ) / N * (2 * (Real.pi : ℂ) * Complex.I) *
      ((eisensteinIntegerNorm n : ℂ) -
        (eisensteinIntegerNorm (((HeckeTheta.residueEquiv N n).1.1 : ℤ),
          ((HeckeTheta.residueEquiv N n).1.2 : ℤ)) : ℂ)) := by ring
    _ = _ := by rw [hkc]; field_simp

/-- Rational translation acts on the finite weight by a norm-dependent phase. -/
def eisensteinRationalTwist {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) (a : ℤ) (r : Fin N × Fin N) : ℂ :=
  w r * eisensteinRationalPhase a N ((r.1 : ℤ), (r.2 : ℤ))

theorem periodicCoeff_eisensteinRationalTwist {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) (a : ℤ) (n : ℤ × ℤ) :
    HeckeTheta.periodicCoeff (eisensteinRationalTwist w a) n =
      HeckeTheta.periodicCoeff w n * eisensteinRationalPhase a N n := by
  rw [eisensteinRationalPhase_residue a N n]
  rfl

theorem eisensteinGaussian_rational_translate {N : ℕ} [NeZero N]
    (a : ℤ) (τ : ℍ) (n : ℤ × ℤ) :
    eisensteinComplexGaussian
      (eisensteinGaussianParameter (((a : ℝ) / N) +ᵥ τ)) n =
      eisensteinRationalPhase a N n *
        eisensteinComplexGaussian (eisensteinGaussianParameter τ) n := by
  unfold eisensteinComplexGaussian eisensteinGaussianParameter eisensteinRationalPhase
  rw [← Complex.exp_add]
  congr 1
  simp only [UpperHalfPlane.coe_vadd, Complex.ofReal_div, Complex.ofReal_intCast,
    Complex.ofReal_natCast]
  unfold eisensteinIntegerNorm
  push_cast
  ring

/-- Exact translation of convergent theta functions, with no modularity assumption. -/
theorem weightedEisensteinTheta_rational_translate {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) (a : ℤ) (τ : ℍ) :
    weightedEisensteinTheta w (((a : ℝ) / N) +ᵥ τ) =
      weightedEisensteinTheta (eisensteinRationalTwist w a) τ := by
  unfold weightedEisensteinTheta eisensteinWeightedGaussian
  apply tsum_congr
  intro n
  rw [eisensteinGaussian_rational_translate, periodicCoeff_eisensteinRationalTwist]
  ring

end ArtinMatthews
