module

public import ArtinMatthews.MarkedPhysicalActualPositionMoment
public import ArtinMatthews.MarkedPhysicalCoordinateLineGlobal
public import ArtinMatthews.MarkedPhysicalIndexDampingFormula
public import ArtinMatthews.MarkedPhysicalMomentCappedApproximation
public import ArtinMatthews.MarkedPhysicalSourceErrorScale
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

/-! The only conditional analytic input is a bound on the actual
capped main term. The original matrix moment and its normalization
are then controlled by the proved source approximation. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalActualPositionMoment_of_capped_bound
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) {δ : ℝ} (hδ : 0 < δ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (K Hexp B etaBound psiBound Qexp G : ℝ)
    (hK : 0 ≤ K) (hHexp : 0 ≤ Hexp) (hB : 8 ≤ B)
    (heta : 0 ≤ etaBound) (hpsi : 0 ≤ psiBound) (hQexp : 0 ≤ Qexp) (hG : 0 ≤ G)
    (hη : ∀ t,‖η t‖ ≤ etaBound) (hψ : ∀ t,‖ψ t‖ ≤ psiBound)
    (hψsupport : Function.support ψ ⊆ Set.Icc (-K) K) :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ) (hd₀ : 0 < d₀)
      (hY : Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y), Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      d₀*Y ≤ Real.exp (Hexp*(Real.log x)^(21/100:ℝ)) →
      ∀ (q U V : ℝ),0 ≤ q → q ≤ 1 → x^δ ≤ U → x^δ ≤ V →
      let R := markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)
      let hR := markedPhysicalMomentTubeRadius_ge_one (markedMemoryMomentLength x) hK
        (mul_nonneg hd₀.le ((Real.exp_pos _).le.trans hY))
      ‖markedPhysicalCoordinateCappedGlobal e x ψ η d₀ Y ((Real.log x)^Qexp) q U V R hR‖ ≤
        15*(Real.log x)^(-(G+1)*(markedMemoryMomentLength x:ℝ)) →
      ∀ (w : ↥(markedPhysicalPrimitiveBox U (16*U) V (2*V)) → ℤ × ℤ),
      (∀ a,markedMinorIntegerDet a.1 (w a)=1) →
      markedPhysicalActualPositionMoment e x ψ η d₀ Y ((Real.log x)^Qexp) q U V w/(U*V) ≤
        (Real.log x)^(-G*(markedMemoryMomentLength x:ℝ)) := by
  let F := 1+15/(riemannZeta 2).re
  filter_upwards [markedPhysicalPositionMoment_capped_moment_log_saving e he heUpper hinj hδ
    ψ η K Hexp B etaBound psiBound Qexp (G+1) hK hHexp hB heta hpsi hQexp
      (by linarith) hη hψ hψsupport,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 F))] with x hx hx1 hlog
  intro d₀ Y hd₀ hY hYhi hscale q U V hq0 hq1 hU hV
  dsimp only
  intro hcap w hw
  let R := markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)
  have hR : 1 ≤ R := markedPhysicalMomentTubeRadius_ge_one _ hK
    (mul_nonneg hd₀.le ((Real.exp_pos _).le.trans hY))
  let c := markedPhysicalCoordinateCappedGlobal e x ψ η d₀ Y ((Real.log x)^Qexp) q U V R hR
  let M := markedPhysicalActualPositionMoment e x ψ η d₀ Y ((Real.log x)^Qexp) q U V w
  let p := (Real.log x)^(-(G+1)*(markedMemoryMomentLength x:ℝ))
  let d := U*V/(riemannZeta 2).re
  have hU1 : 1 < U := (Real.one_lt_rpow hx1 hδ).trans_le hU
  have hV1 : 1 < V := (Real.one_lt_rpow hx1 hδ).trans_le hV
  have huv : 0 < U*V := mul_pos (by linarith) (by linarith)
  have hd : 0 ≤ d := div_nonneg huv.le markedRoot_zeta_two_pos.le
  have happ : |M-d*c.re| ≤ p*(U*V) := (div_le_iff₀ huv).mp
    (hx d₀ Y hd₀ hY hYhi hscale q U V hq0 hq1 hU hV w hw)
  have hc : c.re ≤ 15*p := (Complex.re_le_norm c).trans hcap
  have hmain : M ≤ (F*p)*(U*V) := by
    have h1 := (le_abs_self (M-d*c.re)).trans happ
    have h2 := mul_le_mul_of_nonneg_left hc hd
    have hEq : d*(15*p)+p*(U*V)=(F*p)*(U*V) := by dsimp [d,F]; ring
    linarith
  apply ((div_le_iff₀ huv).mpr hmain).trans
  exact markedPhysicalSourceErrorScale ((le_max_left _ _).trans hlog)
    ((le_max_right _ _).trans hlog) (markedPhysicalMomentLength_pos hx1)

end
end ArtinMatthews
