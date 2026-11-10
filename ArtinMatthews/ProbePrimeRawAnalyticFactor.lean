module

public import ArtinMatthews.ProbeEulerRegions
public import ArtinMatthews.ProbePrimeRawSeries
public import ArtinMatthews.ProbePrimeRawEuler
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Complex-power specialization of the literal j=0 local series to the
named rational factor used by the analytic Euler-product construction. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField Classical
noncomputable section

theorem probe_cpow_local_geometric (q : ℂ) (hq : q ≠ 0) (x z : ℂ) :
    q ^ 4 * (q ^ (-x)) ^ 6 * q ^ (-(6 * z)) = q ^ (4 - 6 * x - 6 * z) := by
  rw [← Complex.cpow_natCast q 4, ← Complex.cpow_nat_mul q 6 (-x),
    ← Complex.cpow_add _ _ hq, ← Complex.cpow_add _ _ hq]
  congr 1
  ring

variable (K : Type*) [Field K] [NumberField K]

theorem probePrimeRawLocal_analytic_factor (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ Ideal.span {p}) ≠ 2)
    (η θ x w z : ℂ) (hθ : θ ^ 6 = 1) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let v := probePrimeGaussLocalVartheta K p hp.ne_zero χ η
    ‖ArtinMatthews.probeLocalV Q z‖ < 1 →
    ‖ArtinMatthews.probeLocalW Q θ w‖ < 1 →
    ‖ArtinMatthews.probeLocalE Q (v ^ 6) x z‖ < 1 →
    probePrimeRawLocalSeries K p hp.ne_zero χ η θ ((Q : ℂ) ^ (-x))
      ((Q : ℂ) ^ (-w)) (ArtinMatthews.probeLocalV Q z) =
      ArtinMatthews.probeGoodLocalFactor (Q : ℂ)
        (ArtinMatthews.probeLocalV Q z) (ArtinMatthews.probeLocalW Q θ w)
        (ArtinMatthews.probeLocalD Q (η * θ⁻¹) x)
        (ArtinMatthews.probeLocalE Q (v ^ 6) x z) := by
  dsimp only
  intro hV hW hE
  have hq : (Ideal.absNorm (Ideal.span {p}) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  have he : (probePrimeGaussLocalVartheta K p hp.ne_zero χ η) ^ 6 *
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 4 *
      ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-x)) ^ 6 *
      ArtinMatthews.probeLocalV (Ideal.absNorm (Ideal.span {p})) z =
      ArtinMatthews.probeLocalE (Ideal.absNorm (Ideal.span {p}))
        ((probePrimeGaussLocalVartheta K p hp.ne_zero χ η) ^ 6) x z := by
    simp only [ArtinMatthews.probeLocalV, ArtinMatthews.probeLocalE, Complex.ofReal_natCast]
    rw [mul_assoc, mul_assoc]
    congr 1
    simpa only [mul_assoc] using probe_cpow_local_geometric _ hq x z
  have h := probePrimeRawLocalSeries_eq K p hp χ hχ hminus hchar η θ
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-x))
    ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w))
    (ArtinMatthews.probeLocalV (Ideal.absNorm (Ideal.span {p})) z) hθ hV hW (he.symm ▸ hE)
  rw [he] at h
  simpa only [ArtinMatthews.probeLocalW, ArtinMatthews.probeLocalD,
    Complex.ofReal_natCast, mul_assoc] using h

theorem probePrimeRawLocal_analytic_correction (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ Ideal.span {p}) ≠ 2)
    (η θ x w z : ℂ) (hθ : θ ^ 6 = 1) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let v := probePrimeGaussLocalVartheta K p hp.ne_zero χ η
    ‖ArtinMatthews.probeLocalV Q z‖ < 1 →
    ‖ArtinMatthews.probeLocalW Q θ w‖ < 1 →
    ‖ArtinMatthews.probeLocalE Q (v ^ 6) x z‖ < 1 →
    (1 - ArtinMatthews.probeLocalV Q z) * (1 - ArtinMatthews.probeLocalW Q θ w) /
      (1 - ArtinMatthews.probeLocalD Q (η * θ⁻¹) x) *
      probePrimeRawLocalSeries K p hp.ne_zero χ η θ ((Q : ℂ) ^ (-x))
        ((Q : ℂ) ^ (-w)) (ArtinMatthews.probeLocalV Q z) =
      ArtinMatthews.probeGoodPrimeCorrection Q θ (η * θ⁻¹) (v ^ 6) x w z := by
  dsimp only
  intro hV hW hE
  rw [probePrimeRawLocal_analytic_factor K p hp χ hχ hminus hchar η θ x w z hθ hV hW hE]
  rfl

end

end ArtinMatthews.VaryingKummerAnalytic
