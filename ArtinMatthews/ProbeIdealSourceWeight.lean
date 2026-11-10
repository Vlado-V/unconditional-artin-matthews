module

public import ArtinMatthews.ProbeIdealLocalCoefficient
public import ArtinMatthews.ProbeBadPrimeRegions
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

/-! The literal source coefficient and complex norm weight at any ideal prime. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def probeIdealSourceTerm (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (j : ℕ)
    (γ ν θ ξ w z : ℂ) (e : Fin 2) (l k m : ℕ) : ℂ :=
  probeIdealLocalCoefficient K P χ (e.val + 3 * l) k (j + 6 * m) *
    γ ^ e.val * ν ^ (e.val + 3 * l) * θ ^ k * (θ⁻¹) ^ (e.val + 3 * l) *
      (Ideal.absNorm P.asIdeal : ℂ) ^
        (-((e.val : ℂ) * (1 / 2 + ξ) + (l : ℂ) * (1 + 3 * ξ) + (k : ℂ) * w + (6 * m : ℂ) * z))

def probeIdealSourceWeight (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (j : ℕ)
    (A B W V : ℂ) (e : Fin 2) (l k m : ℕ) : ℂ :=
  probeIdealLocalCoefficient K P χ (e.val + 3 * l) k (j + 6 * m) *
    A ^ e.val * B ^ l * W ^ k * V ^ m

theorem probeIdealSourceWeight_eq_source (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (j : ℕ)
    (γ ν θ ξ w z : ℂ) (e : Fin 2) (l k m : ℕ) :
    let Q : ℝ := Ideal.absNorm P.asIdeal
    probeIdealSourceWeight K P χ j (probeBadFirstParameter Q γ ν θ ξ)
      (probeBadThetaParameter Q ν θ ξ) (ArtinMatthews.probeLocalW Q θ w)
      (ArtinMatthews.probeLocalV Q z) e l k m =
      probeIdealSourceTerm K P χ j γ ν θ ξ w z e l k m := by
  let Q : ℂ := Ideal.absNorm P.asIdeal
  have hQ : Q ≠ 0 := by
    dsimp only [Q]
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot
  have hpow : (Q ^ (-(1 / 2 + ξ))) ^ e.val * (Q ^ (-(1 + 3 * ξ))) ^ l *
      (Q ^ (-w)) ^ k * (Q ^ (-(6 * z))) ^ m =
      Q ^ (-((e.val : ℂ) * (1 / 2 + ξ) + (l : ℂ) * (1 + 3 * ξ) + (k : ℂ) * w + (6 * m : ℂ) * z)) := by
    rw [← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat,
      ← Complex.cpow_add _ _ hQ, ← Complex.cpow_add _ _ hQ, ← Complex.cpow_add _ _ hQ]
    congr 1
    ring
  dsimp only
  unfold probeIdealSourceWeight probeBadFirstParameter probeBadThetaParameter
    ArtinMatthews.probeLocalW ArtinMatthews.probeLocalV probeIdealSourceTerm
  simp only [Complex.ofReal_natCast]
  change _ = _ * γ ^ e.val * ν ^ (e.val + 3 * l) * θ ^ k * (θ⁻¹) ^ (e.val + 3 * l) * _
  calc
    _ = probeIdealLocalCoefficient K P χ (e.val + 3 * l) k (j + 6 * m) *
        γ ^ e.val * ν ^ (e.val + 3 * l) * θ ^ k * (θ⁻¹) ^ (e.val + 3 * l) *
          ((Q ^ (-(1 / 2 + ξ))) ^ e.val * (Q ^ (-(1 + 3 * ξ))) ^ l *
            (Q ^ (-w)) ^ k * (Q ^ (-(6 * z))) ^ m) := by
      simp only [pow_add, pow_mul, mul_pow]
      ring
    _ = _ := by rw [hpow]

def probeIdealSourceSeries (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (j : ℕ) (γ ν θ ξ w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' i : ℕ × (ℕ × ℕ),
    probeIdealSourceTerm K P χ j γ ν θ ξ w z e i.2.1 i.1 i.2.2

end
end ArtinMatthews.VaryingKummerAnalytic
