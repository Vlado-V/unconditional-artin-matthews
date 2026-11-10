module

public import ArtinMatthews.ProbeBadIdealHolomorphy
public import ArtinMatthews.ProbeIdealGaussPhase
public import ArtinMatthews.ProbeIdealCoefficientBounds
public import ArtinMatthews.ProbeIdealGaussValues
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual unitary Gauss phases and jointly holomorphic bad factors at
arbitrary prime ideals. The data no longer require a prime generator. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain Set
open scoped NumberField Classical BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem probeBadIdealGaussGamma_norm_one (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (j : ℕ) (hj : 0 < j) (hj6 : j < 6) :
    ‖probeIdealGaussGamma K P χ j‖ = 1 := by
  have hn : χ ^ j ≠ 1 := by
    intro he
    have hd := (orderOf_dvd_iff_pow_eq_one).mpr he
    rw [hχ] at hd
    exact (Nat.not_le_of_gt hj6) (Nat.le_of_dvd hj hd)
  have hQ : 0 < (Ideal.absNorm P.asIdeal : ℝ) :=
    lt_of_lt_of_le zero_lt_one (probeIdealNorm_one_le K P)
  rw [probeIdealGaussGamma, norm_div, probeIdealTau_norm K P (χ ^ j) hn,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_self (Real.sqrt_pos.mpr hQ).ne'

theorem probeBadIdealGaussLocalVartheta_norm (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hchar : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2) (η : ℂ) :
    ‖probeIdealGaussLocalVartheta K P χ η‖ = ‖η‖ := by
  have h := congrArg norm (probeIdealGauss_vartheta_phase K P χ hχ hchar η)
  simpa only [norm_mul, norm_neg,
    probeBadIdealGaussGamma_norm_one K P χ hχ 1 (by decide) (by decide),
    probeBadIdealGaussGamma_norm_one K P χ hχ 2 (by decide) (by decide), one_mul] using h

omit [NumberField K] in
theorem probeBadIdealCharacter_unit_norm (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (u : ((𝓞 K) ⧸ P.asIdeal)ˣ) : ‖χ (u : (𝓞 K) ⧸ P.asIdeal)‖ = 1 := by
  have h6 : χ ^ 6 = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rw [hχ])
  have hpow : χ (u : (𝓞 K) ⧸ P.asIdeal) ^ 6 = 1 := by
    rw [← χ.pow_apply' (by decide : 6 ≠ 0), h6, MulChar.one_apply u.isUnit]
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : 6 ≠ 0)).mp
  rw [← norm_pow, hpow, norm_one]

structure ProbeBadIdealData (P : HeightOneSpectrum (𝓞 K)) where
  character : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ
  order_six : orderOf character = 6
  minus_one : character (-1) = 1
  residue_char_ne_two : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2
  eta : ℂ
  eta_norm : ‖eta‖ = 1
  unit : ((𝓞 K) ⧸ P.asIdeal)ˣ
  valuation : ℕ
  valuation_pos : 0 < valuation
  valuation_lt_six : valuation < 6
  norm_large : (ArtinMatthews.probeEulerCutoff : ℝ) ≤ Ideal.absNorm P.asIdeal

namespace ProbeBadIdealData

variable {K : Type*} [Field K] [NumberField K] {P : HeightOneSpectrum (𝓞 K)}
variable (D : ProbeBadIdealData K P)

def gamma : ℂ := probeIdealGaussGamma K P D.character 2
def vartheta : ℂ := probeIdealGaussLocalVartheta K P D.character D.eta
def theta : ℂ := D.character (D.unit : (𝓞 K) ⧸ P.asIdeal)

theorem phase_norms : ‖D.gamma‖ = 1 ∧ ‖D.vartheta‖ = 1 ∧ ‖D.theta‖ = 1 := by
  refine ⟨probeBadIdealGaussGamma_norm_one K P D.character D.order_six 2 (by decide) (by decide), ?_, ?_⟩
  · rw [vartheta, probeBadIdealGaussLocalVartheta_norm K P D.character D.order_six
      D.residue_char_ne_two, D.eta_norm]
  · exact probeBadIdealCharacter_unit_norm K P D.character D.order_six D.unit

def correction : ArtinMatthews.ProbeCoordinates → ℂ :=
  probeBadIdealSourceCorrection K P D.character D.valuation D.gamma D.vartheta D.theta

theorem correction_differentiableOn :
    DifferentiableOn ℂ D.correction (interior ArtinMatthews.probeEulerDomain) := by
  obtain ⟨hγ, hν, hθ⟩ := D.phase_norms
  exact probeBadIdealSourceCorrection_differentiableOn K P D.character D.order_six D.minus_one
    D.valuation D.valuation_pos D.gamma D.vartheta D.theta hγ hν hθ D.norm_large

theorem correction_differentiableOn_open :
    DifferentiableOn ℂ D.correction ArtinMatthews.probeEulerOpenDomain :=
  D.correction_differentiableOn.mono ArtinMatthews.probeEulerOpenDomain_subset_interior

end ProbeBadIdealData

def probeBadIdealFiniteProduct (T : Finset (HeightOneSpectrum (𝓞 K)))
    (D : ∀ P : T, ProbeBadIdealData K P.val) (q : ArtinMatthews.ProbeCoordinates) : ℂ :=
  ∏ P : T, (D P).correction q

theorem probeBadIdealFiniteProduct_differentiableOn (T : Finset (HeightOneSpectrum (𝓞 K)))
    (D : ∀ P : T, ProbeBadIdealData K P.val) :
    DifferentiableOn ℂ (probeBadIdealFiniteProduct K T D)
      (interior ArtinMatthews.probeEulerDomain) := by
  intro q hq
  have hprod (s : Finset T) : DifferentiableWithinAt ℂ
      (fun q : ArtinMatthews.ProbeCoordinates => ∏ P ∈ s, (D P).correction q)
      (interior ArtinMatthews.probeEulerDomain) q := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact differentiableWithinAt_const (1 : ℂ)
    | @insert P s hP ih =>
      simp only [Finset.prod_insert hP]
      exact ((D P).correction_differentiableOn q hq).mul ih
  exact hprod Finset.univ

end
end ArtinMatthews.VaryingKummerAnalytic
