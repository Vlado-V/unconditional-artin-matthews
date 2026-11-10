module

public import ArtinMatthews.MarkedPhysicalTypeIIGoodPairing
public import ArtinMatthews.MarkedPhysicalCoordinateLineGlobal
public import ArtinMatthews.MarkedEstimateMertensBands
public import ArtinMatthews.MarkedPhysicalMomentFromCapped
public import ArtinMatthews.MarkedPhysicalSourceErrorScale
public import ArtinMatthews.MarkedPhysicalTypeIICellBudget
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual centered Type II endpoints and the original localized
moment give every logarithmic saving. The sole pending input is a
bound on the literal capped global term, at its original radius. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalTypeIIGoodPairing_of_capped_bound
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) {δ : ℝ} (hδ : 0 < δ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (K Hexp B etaBound psiBound Qexp C P : ℝ)
    (hK : 0 ≤ K) (hHexp : 0 ≤ Hexp) (hB : 8 ≤ B)
    (heta : 0 ≤ etaBound) (hpsi : 0 ≤ psiBound) (hQexp : 0 ≤ Qexp)
    (hC : 0 ≤ C) (hP : 0 ≤ P)
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
        15*(Real.log x)^(-(P+2*C+6)*(markedMemoryMomentLength x:ℝ)) →
      ∀ (w : ↥(markedPhysicalPrimitiveBox U (16*U) V (2*V)) → ℤ × ℤ),
      (∀ a,markedMinorIntegerDet a.1 (w a)=1) →
      ∀ (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ),
      (∀ n∈Sα,x^δ ≤ (n:ℝ)) → (∀ n∈Sβ,‖β n‖ ≤ (Real.log x)^C) →
      ‖markedPhysicalTypeIIGoodPairing e x ψ η d₀ Y ((Real.log x)^Qexp) q U V w
        Sα Sβ modulation β‖ ≤ (U*V)*(Real.log x)^(-P) := by
  let G := P+2*C+5
  let F := 32*Real.sqrt (2*(⌈2*K+1⌉₊:ℝ)+1)*(257*Real.exp Hexp)
  have he0 : ∀ j,0 < e j := fun j => lt_of_lt_of_le (by norm_num) (he j)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hbands := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually (he0 j))
  filter_upwards [markedPhysicalActualPositionMoment_of_capped_bound e he heUpper hinj hδ
    ψ η K Hexp B etaBound psiBound Qexp G hK hHexp hB heta hpsi hQexp hG hη hψ hψsupport,
    markedPhysicalTypeIIEndpoint_bounds e he0 hinj δ C hδ,hbands,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 F))]
    with x hm hept hb hx hlog
  intro d₀ Y hd₀ hY hYhi hscale q U V hq0 hq1 hU hV
  dsimp only
  intro hcap w hw Sα Sβ modulation β hSα hβ
  have hUp : 0 < U := (Real.rpow_pos_of_pos (zero_lt_one.trans hx) δ).trans_le hU
  have hVp : 0 < V := (Real.rpow_pos_of_pos (zero_lt_one.trans hx) δ).trans_le hV
  have huv : 0 < U*V := mul_pos hUp hVp
  have hL : 1 ≤ Real.log x := (le_max_left _ _).trans hlog
  have hYp : 0 < Y := (Real.exp_pos _).trans_le hY
  have hmass (j) : 0 < bandReciprocalMass (markedLogPowerBand (e j) x) :=
    (show 0 < Real.log 2/2 by positivity).trans (hb j).1
  have hshift : G+1=P+2*C+6 := by dsimp [G]; ring
  have hcap' : ‖markedPhysicalCoordinateCappedGlobal e x ψ η d₀ Y ((Real.log x)^Qexp)
      q U V (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y))
      (markedPhysicalMomentTubeRadius_ge_one _ hK (mul_nonneg hd₀.le hYp.le))‖ ≤
      15*(Real.log x)^(-(G+1)*(markedMemoryMomentLength x:ℝ)) := by
    rw [hshift]
    exact hcap
  have ht := (div_le_iff₀ huv).mp
    (hm d₀ Y hd₀ hY hYhi hscale q U V hq0 hq1 hU hV hcap' w hw)
  have heps := hept U V hUp hVp Sα Sβ modulation β hSα hβ
  have hp := markedPhysicalTypeIIGoodPairing_moment_bound e x hx hmass ψ η d₀ Y
    ((Real.log x)^Qexp) q K U V C G hd₀ hYp hK hUp hVp hψsupport w
    Sα Sβ modulation β heps.1 heps.2 (by simpa only [mul_comm] using ht)
  have hc := markedPhysicalTypeII_cell_root_bound hL (mul_pos hd₀ hYp).le hHexp hscale
  have hexp : 2*C+4-G=-(P+1) := by dsimp [G]; ring
  rw [hexp] at hp
  have hs : F*(Real.log x)^(-(P+1)) ≤ (Real.log x)^(-P) := by
    simpa only [Nat.cast_one,mul_one] using
      (markedPhysicalSourceErrorScale (N:=1) (G:=P) hL ((le_max_right _ _).trans hlog) (by norm_num))
  calc
    _ ≤ 32*Real.sqrt (2*(⌈2*K+1⌉₊:ℝ)+1)*
        (256*(d₀*Y)+1)^((markedMemoryMomentLength x:ℝ)⁻¹)*
        (U*V)*(Real.log x)^(-(P+1)) := hp
    _ ≤ 32*Real.sqrt (2*(⌈2*K+1⌉₊:ℝ)+1)*(257*Real.exp Hexp)*
        (U*V)*(Real.log x)^(-(P+1)) := by gcongr
    _ = (U*V)*(F*(Real.log x)^(-(P+1))) := by dsimp [F]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs huv.le

end
end ArtinMatthews
