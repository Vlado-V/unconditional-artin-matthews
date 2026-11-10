module

public import ArtinMatthews.PrincipalAngularGaussian
public import ArtinMatthews.PrincipalAngularSignalDecay
public import ArtinMatthews.PrincipalAngularSignalMellin
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! The actual primitive source identity with its angular correction and
finite Euler factors. The sole analytic improvement left as input is a power
bound for this literal corrected signal at infinity. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set Filter Asymptotics Complex
open OAI.SevenEighths OAI.SevenEighths.Continuation
open scoped NumberField Classical Topology FourierTransform
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {ζ : K} {M : Ideal (𝓞 K)}
variable (hζ : IsPrimitiveRoot ζ 12) (η : EvenIdealRayCharacter K M)
  (hM : M ≠ ⊥) (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals η.residue)
  (hnp : η.IsNonprincipal) (S : Finset (ArtinMatthews.ProbePrime K))
  (hS : principalAngularCutoff K M ⊆ S)
include hnp hS

theorem primitiveContinued_mul_angularEuler_mellin
    (a : ℝ) (ha₀ : 99799 / 100000 ≤ a) (ha : a < 2)
    (htop : principalAngularGaussianSignal hζ η S =O[atTop]
      (fun x : ℝ => x ^ (a + (-8 / 15 : ℝ))))
    {s : ℂ} (hs : a < s.re) :
    (η.primitiveContinued hM hprim s * principalAngularRayEulerFactor η S s) *
      signalMellin (principalAngularGaussianSignal hζ η S) (-8 / 15) s =
        Complex.exp ((s - 5 / 6) ^ 2) * principalAngularCorrection hζ η S s := by
  have hL : AnalyticOnNhd ℂ
      (fun s => η.primitiveContinued hM hprim s * principalAngularRayEulerFactor η S s)
      {s : ℂ | a < s.re} := by
    intro s _
    exact ((η.primitiveContinued_entire hM hprim).mul
      (principalAngularRayEulerFactor_entire η S)).analyticAt s
  have hF := signalMellin_analytic (principalAngularGaussianSignal hζ η S) a (-8 / 15)
    (principalAngularGaussianSignal_locallyIntegrable hζ η S hS) htop
    (principalAngularGaussianSignal_rapidDecayAtZero hζ η S hS)
  have hH : AnalyticOnNhd ℂ (principalAngularCorrection hζ η S) {s : ℂ | a < s.re} :=
    (principalAngularCorrection_analyticOnNhd hζ η S hS).mono
      (fun _ hz => lt_of_le_of_lt ha₀ hz)
  have hW : AnalyticOnNhd ℂ
      (fun s : ℂ => Complex.exp ((s - 5 / 6) ^ 2) * principalAngularCorrection hζ η S s)
      {s : ℂ | a < s.re} :=
    (((analyticOnNhd_id.sub analyticOnNhd_const).pow 2).cexp).mul hH
  have heq : ∀ s : ℂ, max a 1 < s.re →
      (η.primitiveContinued hM hprim s * principalAngularRayEulerFactor η S s) *
        signalMellin (principalAngularGaussianSignal hζ η S) (-8 / 15) s =
          Complex.exp ((s - 5 / 6) ^ 2) * principalAngularCorrection hζ η S s := by
    intro s hs'
    have hright := (le_max_right a 1).trans_lt hs'
    rw [principalAngularGaussianSignal_mellin_eq_amplitude hζ η S hS a ha htop hs',
      η.primitiveContinued_eq_dirichlet hM hprim hnp hright]
    change principalAngularExteriorL η S s *
      (Complex.exp ((s - 5 / 6) ^ 2) *
        (principalAngularCorrection hζ η S s * (principalAngularExteriorL η S s)⁻¹)) = _
    have hn := principalAngularExteriorL_ne_zero η S hright
    field_simp
  exact product_identity_on_halfPlane a 1
    (fun s => η.primitiveContinued hM hprim s * principalAngularRayEulerFactor η S s)
    (signalMellin (principalAngularGaussianSignal hζ η S) (-8 / 15))
    (fun s => Complex.exp ((s - 5 / 6) ^ 2) * principalAngularCorrection hζ η S s)
    hL hF hW heq hs

theorem primitiveContinued_ne_zero_of_angularSignal_power_bound
    (a : ℝ) (ha₀ : 99799 / 100000 ≤ a) (ha : a < 2)
    (htop : principalAngularGaussianSignal hζ η S =O[atTop]
      (fun x : ℝ => x ^ (a + (-8 / 15 : ℝ))))
    {ρ : ℂ} (hρ : a < ρ.re) : η.primitiveContinued hM hprim ρ ≠ 0 := by
  have h := primitiveContinued_mul_angularEuler_mellin hζ η hM hprim hnp S hS
    a ha₀ ha htop hρ
  intro hz
  rw [hz, zero_mul, zero_mul] at h
  exact (mul_ne_zero (Complex.exp_ne_zero _)
    (principalAngularCorrection_ne_zero hζ η S hS (ha₀.trans hρ.le))) h.symm

/-- The manuscript width `10⁻⁶` uses the exact fixed source exponent.
No constant or onset uniform in the character or field is required here. -/
theorem primitiveContinued_ne_zero_of_angularSignal_manuscript_bound
    (htop : principalAngularGaussianSignal hζ η S =O[atTop]
      (fun x : ℝ => x ^ (1 - 1 / 1000000 - 8 / 15 : ℝ)))
    {ρ : ℂ} (hρ : 1 - 1 / 1000000 < ρ.re) :
    η.primitiveContinued hM hprim ρ ≠ 0 := by
  apply primitiveContinued_ne_zero_of_angularSignal_power_bound hζ η hM hprim hnp S hS
    (1 - 1 / 1000000) (by norm_num) (by norm_num) _ hρ
  convert htop using 1
  norm_num

/-- The exact exponent in source06 implies the literal manuscript width. -/
theorem primitiveContinued_ne_zero_of_angularSignal_source06_bound
    (htop : principalAngularGaussianSignal hζ η S =O[atTop]
      (fun x : ℝ => x ^ (7 / 15 - 1 / 20000 : ℝ)))
    {ρ : ℂ} (hρ : 1 - 1 / 1000000 < ρ.re) :
    η.primitiveContinued hM hprim ρ ≠ 0 := by
  apply primitiveContinued_ne_zero_of_angularSignal_power_bound hζ η hM hprim hnp S hS
    (1 - 1 / 20000) (by norm_num) (by norm_num) _ (by linarith)
  convert htop using 1
  norm_num

end
end ArtinMatthews.VaryingKummerAnalytic
