module

public import ArtinMatthews.MarkedPhysicalCappedGoodVolume
public import ArtinMatthews.MarkedRootTubeBoundary
public import ArtinMatthews.MarkedEstimateMertensBands
public import ArtinMatthews.MarkedRootTubeBoundaryActual
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! The exact decorated good-volume sum inherits the original signed
word bound. Actual band masses discharge its normalization conditions;
the independent-line baseline product is not part of this sum. -/

noncomputable section
namespace ArtinMatthews
open Filter MeasureTheory

set_option backward.isDefEq.respectTransparency false in
theorem markedPhysicalCappedGoodVolumeSum_actual_bound
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ)≤e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ u,‖η u‖≤1)
    (q ρ G H A W : ℝ) (hq₀ : 0≤q) (hq₁ : q≤1)
    (hρ : 0<ρ) (hρ₁ : ρ<1) (hgap : Real.sqrt q<ρ^2)
    (hG : 0<G) (hH : 1≤H) (hA : 0≤A) (hW : 0≤W)
    (hdepth : 100*(5*G+36)<(Fintype.card J:ℝ))
    (hψ : ∀ u,‖ψ u‖≤W) (hsupp : Function.support ψ ⊆ Set.Icc (-A) A) :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ),0<d₀ →
      Real.exp ((Real.log x)^(1/10:ℝ))≤Y →
      Y≤Real.exp (H*(Real.log x)^(1/5:ℝ)) →
      ∀ (R : ℕ) (hR : 1≤R) (U V : ℝ)
        (hdis : ∀ j k,j≠k → Disjoint (markedRawActualPrimeBand e x j) (markedRawActualPrimeBand e x k)),
      ‖markedPhysicalCappedGoodVolumeSum (B := markedDirtyMemoryCutoff x)
        (n := markedMemoryMomentLength x) e x (markedRootTubePrimitive R) hdis
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) ψ η d₀ Y
        ((Real.log x)^(G+9)) q U V hR (markedRootTubeOrigin R hR)‖≤
        15*((Real.log x)^(-G))^(markedMemoryMomentLength x) := by
  have hbands := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/10) (he j)))
  filter_upwards [markedRootTubeBoundary_integral_actual_bound e he hinj ψ η hη hηnorm
    q ρ G H A W hq₀ hq₁ hρ hρ₁ hgap hG hH hA hW hdepth hψ hsupp,
    hbands,eventually_gt_atTop (1:ℝ)] with x hx hb hx₁
  intro d₀ Y hd₀ hYlo hYhi R hR U V hdis
  have hV : ∀ j,bandReciprocalMass (markedLogPowerBand (e j) x)≠0 := by
    intro j
    exact ne_of_gt ((show (0:ℝ)<Real.log 2/2 by positivity).trans (hb j).1)
  have hn : 0 < markedMemoryMomentLength x := by
    unfold markedMemoryMomentLength
    exact Nat.mul_pos (by norm_num) (Nat.ceil_pos.mpr
      (div_pos (Real.rpow_pos_of_pos (Real.log_pos hx₁) _) (by norm_num)))
  have hi := markedPhysicalBirthDistinctBoundary_integral_eq_cappedGoodVolume
    (B := markedDirtyMemoryCutoff x) (n := markedMemoryMomentLength x)
    e x (markedRootTubePrimitive R) hdis
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) ψ η d₀ Y ((Real.log x)^(G+9))
    q U V hR (markedRootTubeOrigin R hR) hn rfl hV ρ hρ.ne'
  rw [← hi]
  exact hx d₀ Y hd₀ hYlo hYhi R hR U V markedMemoryAlternatingOrientation

end ArtinMatthews
