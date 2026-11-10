module

public import ArtinMatthews.ProbeEulerHolomorphy
public import ArtinMatthews.ProbeIdealSourceWeight
public import ArtinMatthews.ProbeBadIdealNormalSeries
public import ArtinMatthews.ProbeBadPrimeHolomorphy
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

/-! Uniform convergence and joint holomorphy of the literal bad-prime
source series for every prime ideal, without a principal-generator hypothesis. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain Set Filter
open scoped NumberField Classical BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem probeBadIdealSource_tendstoUniformlyOn (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j)
    (γ ν θ : ℂ) (hγ : ‖γ‖ = 1) (hν : ‖ν‖ = 1) (hθ : ‖θ‖ = 1)
    (hcut : (ArtinMatthews.probeEulerCutoff : ℝ) ≤ Ideal.absNorm P.asIdeal)
    (e : Fin 2) :
    TendstoUniformlyOn
      (fun t : Finset (ℕ × (ℕ × ℕ)) => fun q : ArtinMatthews.ProbeCoordinates =>
        ∑ i ∈ t, probeIdealSourceTerm K P χ j γ ν θ q.1 q.2.1 q.2.2
          e i.2.1 i.1 i.2.2)
      (fun q : ArtinMatthews.ProbeCoordinates =>
        ∑' i : ℕ × (ℕ × ℕ), probeIdealSourceTerm K P χ j γ ν θ
          q.1 q.2.1 q.2.2 e i.2.1 i.1 i.2.2)
      atTop ArtinMatthews.probeEulerDomain := by
  apply tendstoUniformlyOn_tsum (probeBadPrimeMajorant_summable
    (Q := (Ideal.absNorm P.asIdeal : ℝ)) (by positivity))
  intro i q hq
  exact probeBadIdealSourceTerm_norm_le_majorant K P χ hχ hminus j hj γ ν θ
    q.1 q.2.1 q.2.2 hγ hν hθ hcut hq e i

theorem probeBadIdealSourceSeries_differentiableOn (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j)
    (γ ν θ : ℂ) (hγ : ‖γ‖ = 1) (hν : ‖ν‖ = 1) (hθ : ‖θ‖ = 1)
    (hcut : (ArtinMatthews.probeEulerCutoff : ℝ) ≤ Ideal.absNorm P.asIdeal) :
    DifferentiableOn ℂ (fun q : ArtinMatthews.ProbeCoordinates =>
      probeIdealSourceSeries K P χ j γ ν θ q.1 q.2.1 q.2.2)
      (interior ArtinMatthews.probeEulerDomain) := by
  unfold probeIdealSourceSeries
  apply DifferentiableOn.fun_sum
  intro e _
  apply probeCoordinates_tsum_differentiableOn _
    (probeBadPrimeMajorant (Ideal.absNorm P.asIdeal))
    (probeBadPrimeMajorant_summable (by positivity))
    (fun i => probeBadIdealSourceTerm_differentiable K P χ j γ ν θ e i)
    _ isOpen_interior
  intro i q hq
  have hq' : q ∈ ArtinMatthews.probeEulerDomain := interior_subset hq
  exact probeBadIdealSourceTerm_norm_le_majorant K P χ hχ hminus j hj γ ν θ
    q.1 q.2.1 q.2.2 hγ hν hθ hcut hq' e i

theorem probeBadIdealSourceSeries_differentiableOn_open (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j)
    (γ ν θ : ℂ) (hγ : ‖γ‖ = 1) (hν : ‖ν‖ = 1) (hθ : ‖θ‖ = 1)
    (hcut : (ArtinMatthews.probeEulerCutoff : ℝ) ≤ Ideal.absNorm P.asIdeal) :
    DifferentiableOn ℂ (fun q : ArtinMatthews.ProbeCoordinates =>
      probeIdealSourceSeries K P χ j γ ν θ q.1 q.2.1 q.2.2)
      ArtinMatthews.probeEulerOpenDomain :=
  (probeBadIdealSourceSeries_differentiableOn K P χ hχ hminus j hj γ ν θ hγ hν hθ hcut).mono
    ArtinMatthews.probeEulerOpenDomain_subset_interior

def probeBadIdealSourceCorrection (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (j : ℕ) (γ ν θ : ℂ)
    (q : ArtinMatthews.ProbeCoordinates) : ℂ :=
  (1 - ArtinMatthews.probeLocalV (Ideal.absNorm P.asIdeal) q.2.2) *
    probeIdealSourceSeries K P χ j γ ν θ q.1 q.2.1 q.2.2

theorem probeBadIdealSourceCorrection_differentiableOn (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j)
    (γ ν θ : ℂ) (hγ : ‖γ‖ = 1) (hν : ‖ν‖ = 1) (hθ : ‖θ‖ = 1)
    (hcut : (ArtinMatthews.probeEulerCutoff : ℝ) ≤ Ideal.absNorm P.asIdeal) :
    DifferentiableOn ℂ (probeBadIdealSourceCorrection K P χ j γ ν θ)
      (interior ArtinMatthews.probeEulerDomain) := by
  have hQ : (Ideal.absNorm P.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot
  have hV : Differentiable ℂ (fun q : ArtinMatthews.ProbeCoordinates =>
      ArtinMatthews.probeLocalV (Ideal.absNorm P.asIdeal) q.2.2) := by
    intro q
    exact ((differentiableAt_id.snd.snd.const_mul 6).neg.const_cpow (Or.inl hQ))
  exact ((differentiableOn_const (c := (1 : ℂ))).sub hV.differentiableOn).mul
    (probeBadIdealSourceSeries_differentiableOn K P χ hχ hminus j hj γ ν θ hγ hν hθ hcut)

theorem probeBadIdealSourceCorrection_differentiableOn_open (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j)
    (γ ν θ : ℂ) (hγ : ‖γ‖ = 1) (hν : ‖ν‖ = 1) (hθ : ‖θ‖ = 1)
    (hcut : (ArtinMatthews.probeEulerCutoff : ℝ) ≤ Ideal.absNorm P.asIdeal) :
    DifferentiableOn ℂ (probeBadIdealSourceCorrection K P χ j γ ν θ)
      ArtinMatthews.probeEulerOpenDomain :=
  (probeBadIdealSourceCorrection_differentiableOn K P χ hχ hminus j hj γ ν θ hγ hν hθ hcut).mono
    ArtinMatthews.probeEulerOpenDomain_subset_interior

end
end ArtinMatthews.VaryingKummerAnalytic
