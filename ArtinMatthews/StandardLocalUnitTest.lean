module

public import ArtinMatthews.StandardLocalBallFourier
public import ArtinMatthews.StandardLocalResidueVolume
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The literal compact-open unit annulus test and its exact scalar
Fourier transform, obtained as the difference of two actual balls. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory StandardAdelic
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (P : HeightOneSpectrum (𝓞 K))

def sourceLocalUnitAnnulus : Set (P.adicCompletion K) :=
  {x | sourceLocalValuation K P x = 1}

def sourceLocalUnitTest : P.adicCompletion K → ℂ :=
  (sourceLocalUnitAnnulus K P).indicator (fun _ => 1)

theorem sourceLocalUnitAnnulus_eq_diff : sourceLocalUnitAnnulus K P =
    sourceLocalBall K P 0 \ sourceLocalBall K P (-1) := by
  ext x
  change sourceLocalValuation K P x = 1 ↔ x ∈ sourceLocalBall K P 0 ∧ x ∉ sourceLocalBall K P (-1)
  rw [sourceLocalPrimeBall_iff]
  change sourceLocalValuation K P x = 1 ↔
    sourceLocalValuation K P x ≤ WithZero.exp (0 : ℤ) ∧ ¬ sourceLocalValuation K P x < 1
  rw [WithZero.exp_zero, not_lt]
  exact le_antisymm_iff

theorem sourceLocalUnitAnnulus_isCompact : IsCompact (sourceLocalUnitAnnulus K P) := by
  rw [sourceLocalUnitAnnulus_eq_diff]
  exact (sourceLocalBall_isCompact K P 0).diff (sourceLocalBall_isOpen K P (-1))

theorem sourceLocalUnitAnnulus_ne_zero {x : P.adicCompletion K} (hx : x ∈ sourceLocalUnitAnnulus K P) : x ≠ 0 := by
  intro he
  change sourceLocalValuation K P x = 1 at hx
  rw [he, map_zero] at hx
  exact zero_ne_one hx

theorem sourceLocalUnitTest_eq_diff : sourceLocalUnitTest K P =
    sourceLocalBallIndicator K P 0 - sourceLocalBallIndicator K P (-1) := by
  funext x
  unfold sourceLocalUnitTest sourceLocalBallIndicator
  rw [sourceLocalUnitAnnulus_eq_diff]
  by_cases hx : x ∈ sourceLocalBall K P (-1)
  · have h₀ := sourceLocalPrimeBall_subset_integer K P hx
    simp [hx, h₀]
  · by_cases h₀ : x ∈ sourceLocalBall K P 0 <;> simp [hx, h₀]

theorem sourceLocalUnitTest_locallyConstant : IsLocallyConstant (sourceLocalUnitTest K P) := by
  rw [sourceLocalUnitTest_eq_diff]
  exact (sourceLocalBallIndicator_locallyConstant K P 0).sub (sourceLocalBallIndicator_locallyConstant K P (-1))

theorem sourceLocalUnitTest_compactSupport : HasCompactSupport (sourceLocalUnitTest K P) := by
  rw [sourceLocalUnitTest_eq_diff]
  exact (sourceLocalBallIndicator_compactSupport K P 0).sub (sourceLocalBallIndicator_compactSupport K P (-1))

theorem sourceLocalBallFourier_integrable_kernel (n : ℤ) (y : P.adicCompletion K) :
    Integrable (fun x => sourceLocalBallIndicator K P n x * localFiniteCharacter K P (-(y * x)))
      (sourceLocalSelfDual K P) := by
  let : (sourceLocalSelfDual K P).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  let g (x : P.adicCompletion K) := localFiniteCharacter K P (-(y * x))
  have hg : Continuous g := (localFiniteCharacter_continuous K P).comp (continuous_const.mul continuous_id).neg
  have h : Integrable ((sourceLocalBall K P n).indicator g) (sourceLocalSelfDual K P) :=
    (hg.continuousOn.integrableOn_compact (sourceLocalBall_isCompact K P n)).integrable_indicator
      (sourceLocalBall_isOpen K P n).measurableSet
  have he : (fun x => sourceLocalBallIndicator K P n x * localFiniteCharacter K P (-(y * x))) =
      (sourceLocalBall K P n).indicator g := by
    funext x
    by_cases hx : x ∈ sourceLocalBall K P n <;> simp [sourceLocalBallIndicator, hx, g]
  rwa [he]

theorem sourceLocalUnitTestFourier_raw (y : P.adicCompletion K) :
    sourceLocalFourier K P (sourceLocalUnitTest K P) y =
      ((sourceLocalSelfDual K P).real (sourceLocalBall K P 0) : ℂ) *
        sourceLocalBallIndicator K P (sourceDifferentExponent K P : ℤ) y -
      ((sourceLocalSelfDual K P).real (sourceLocalBall K P (-1)) : ℂ) *
        sourceLocalBallIndicator K P ((sourceDifferentExponent K P : ℤ) + 1) y := by
  rw [sourceLocalUnitTest_eq_diff]
  have h : sourceLocalFourier K P (sourceLocalBallIndicator K P 0 - sourceLocalBallIndicator K P (-1)) y =
      sourceLocalFourier K P (sourceLocalBallIndicator K P 0) y -
        sourceLocalFourier K P (sourceLocalBallIndicator K P (-1)) y := by
    unfold sourceLocalFourier
    simp only [Pi.sub_apply, sub_mul]
    exact integral_sub (sourceLocalBallFourier_integrable_kernel K P 0 y)
      (sourceLocalBallFourier_integrable_kernel K P (-1) y)
  rw [h, sourceLocalBallFourier, sourceLocalBallFourier]
  simp only [sub_zero, sub_neg_eq_add]

end
end ArtinMatthews.SourcePhysical
