module

public import ArtinMatthews.StandardLocalFourier
public import ArtinMatthews.StandardLocalConductor
public import ArtinMatthews.StandardLocalBall
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init
public import OAI.RepresentationTheory.Weil.Local.NonarchimedeanFourier


set_option backward.privateInPublic true
@[expose] public section

/-! The scalar transform of an actual compact-open valuation ball.
The volume and the exact codifferent radius are both retained. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory StandardAdelic
open OAI.RepresentationTheory.Weil.Local
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (P : HeightOneSpectrum (𝓞 K))

def sourceLocalBallIndicator (n : ℤ) : P.adicCompletion K → ℂ :=
  (sourceLocalBall K P n).indicator (fun _ => 1)

theorem sourceLocalBallIndicator_locallyConstant (n : ℤ) :
    IsLocallyConstant (sourceLocalBallIndicator K P n) :=
  CompactCharacter.Construction.subgroup_indicator_locallyConstant (sourceLocalOpenBall K P n)

theorem sourceLocalBallIndicator_compactSupport (n : ℤ) :
    HasCompactSupport (sourceLocalBallIndicator K P n) :=
  CompactCharacter.Construction.subgroup_indicator_compactSupport (sourceLocalOpenBall K P n)
    (sourceLocalBall_isCompact K P n)

theorem sourceLocalBallFourier (n : ℤ) (y : P.adicCompletion K) :
    sourceLocalFourier K P (sourceLocalBallIndicator K P n) y =
      ((sourceLocalSelfDual K P).real (sourceLocalBall K P n) : ℂ) *
        sourceLocalBallIndicator K P ((sourceDifferentExponent K P : ℤ) - n) y := by
  let μ := sourceLocalSelfDual K P
  let : μ.IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  let χ := (localFiniteCharacter K P).mulShift (-y)
  have h := CompactCharacter.Construction.integral_character_subgroup μ (sourceLocalOpenBall K P n) χ
  change (∫ x in sourceLocalBall K P n, localFiniteCharacter K P ((-y) * x) ∂μ) =
    if ∀ x ∈ sourceLocalBall K P n, localFiniteCharacter K P ((-y) * x) = 1 then
      (μ.real (sourceLocalBall K P n) : ℂ) else 0 at h
  rw [sourceLocalBall_annihilator_iff K P n (-y)] at h
  have hn : -y ∈ sourceLocalBall K P ((sourceDifferentExponent K P : ℤ) - n) ↔
      y ∈ sourceLocalBall K P ((sourceDifferentExponent K P : ℤ) - n) := by
    change sourceLocalValuation K P (-y) ≤ _ ↔ sourceLocalValuation K P y ≤ _
    rw [Valuation.map_neg]
  rw [if_congr hn rfl rfl] at h
  calc
    _ = ∫ x in sourceLocalBall K P n, localFiniteCharacter K P ((-y) * x) ∂μ := by
      rw [← integral_indicator (sourceLocalBall_isOpen K P n).measurableSet]
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun x => ?_
      change sourceLocalBallIndicator K P n x * localFiniteCharacter K P (-(y * x)) = _
      unfold sourceLocalBallIndicator
      by_cases hx : x ∈ sourceLocalBall K P n <;> simp [hx, neg_mul]
    _ = _ := h
    _ = _ := by
      unfold sourceLocalBallIndicator
      by_cases hy : y ∈ sourceLocalBall K P ((sourceDifferentExponent K P : ℤ) - n)
      · simp [hy, μ]
      · simp [hy]

theorem sourceLocalFourier_mulBall_zero (c : ℂ) (n : ℤ) :
    sourceLocalFourier K P (fun x => c * sourceLocalBallIndicator K P n x) 0 =
      c * ((sourceLocalSelfDual K P).real (sourceLocalBall K P n) : ℂ) := by
  unfold sourceLocalFourier
  simp only [zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one]
  rw [integral_const_mul]
  unfold sourceLocalBallIndicator
  rw [integral_indicator (sourceLocalBall_isOpen K P n).measurableSet]
  simp only [integral_const, Measure.restrict_apply_univ, Complex.real_smul, Measure.real, mul_one]

theorem sourceLocalBall_volume_pos (n : ℤ) :
    0 < (sourceLocalSelfDual K P).real (sourceLocalBall K P n) := by
  let : (sourceLocalSelfDual K P).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  exact NonarchimedeanFourier.Construction.compact_open_subgroup_real_pos
    (sourceLocalSelfDual K P) (sourceLocalOpenBall K P n) (sourceLocalBall_isCompact K P n)

theorem sourceLocalSelfDual_volume_product :
    (sourceLocalSelfDual K P).real (sourceLocalBall K P 0) *
      (sourceLocalSelfDual K P).real (sourceLocalBall K P (sourceDifferentExponent K P : ℤ)) = 1 := by
  let a := (sourceLocalSelfDual K P).real (sourceLocalBall K P 0)
  have hF : sourceLocalFourier K P (sourceLocalBallIndicator K P 0) =
      fun y => (a : ℂ) * sourceLocalBallIndicator K P (sourceDifferentExponent K P : ℤ) y := by
    funext y
    simpa only [sub_zero] using sourceLocalBallFourier K P 0 y
  have h := sourceLocalFourier_inversion K P _ (sourceLocalBallIndicator_locallyConstant K P 0)
    (sourceLocalBallIndicator_compactSupport K P 0) 0
  rw [hF, sourceLocalFourier_mulBall_zero] at h
  have hz : sourceLocalBallIndicator K P 0 (-(0 : P.adicCompletion K)) = 1 :=
    Set.indicator_of_mem (show -(0 : P.adicCompletion K) ∈ sourceLocalOpenBall K P 0 by simp) _
  rw [hz] at h
  exact_mod_cast h

theorem sourceLocalSelfDual_volume_integer_of_good (hP : P ∉ traceBadPlaces K) :
    (sourceLocalSelfDual K P).real (sourceLocalBall K P 0) = 1 := by
  let a := (sourceLocalSelfDual K P).real (sourceLocalBall K P 0)
  have h := sourceLocalSelfDual_volume_product K P
  rw [(sourceDifferentExponent_eq_zero_iff K P).mpr hP, Nat.cast_zero] at h
  calc
    a = Real.sqrt (a * a) := (Real.sqrt_mul_self (sourceLocalBall_volume_pos K P 0).le).symm
    _ = 1 := by rw [show a * a = 1 from h, Real.sqrt_one]

end
end ArtinMatthews.SourcePhysical
