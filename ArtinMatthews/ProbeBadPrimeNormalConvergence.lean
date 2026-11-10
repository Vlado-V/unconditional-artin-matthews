module

public import ArtinMatthews.ProbeBadPrimeSourceWeight
public import ArtinMatthews.ProbeEulerLocalHolomorphy
public import ArtinMatthews.ProbeBadPrimeNormalSeries
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

/-! The literal bad-prime partial sums converge uniformly on both
closed enlarged regions, by the actual finite-Gauss majorant. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField Set Filter
open scoped NumberField Classical BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem probeBadPrimeSource_tendstoUniformlyOn (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j)
    (γ ν θ : ℂ) (hγ : ‖γ‖ = 1) (hν : ‖ν‖ = 1) (hθ : ‖θ‖ = 1)
    (hcut : (ArtinMatthews.probeEulerCutoff : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (e : Fin 2) :
    TendstoUniformlyOn
      (fun t : Finset (ℕ × (ℕ × ℕ)) => fun q : ArtinMatthews.ProbeCoordinates =>
        ∑ i ∈ t, probeBadPrimeSourceTerm K p hp.ne_zero χ j γ ν θ q.1 q.2.1 q.2.2
          e i.2.1 i.1 i.2.2)
      (fun q : ArtinMatthews.ProbeCoordinates =>
        ∑' i : ℕ × (ℕ × ℕ), probeBadPrimeSourceTerm K p hp.ne_zero χ j γ ν θ
          q.1 q.2.1 q.2.2 e i.2.1 i.1 i.2.2)
      atTop ArtinMatthews.probeEulerDomain := by
  apply tendstoUniformlyOn_tsum (probeBadPrimeMajorant_summable
    (Q := (Ideal.absNorm (Ideal.span {p}) : ℝ)) (by positivity))
  intro i q hq
  exact probeBadPrimeSourceTerm_norm_le_majorant K p hp χ hχ hminus j hj γ ν θ
    q.1 q.2.1 q.2.2 hγ hν hθ hcut hq e i

end
end ArtinMatthews.VaryingKummerAnalytic
