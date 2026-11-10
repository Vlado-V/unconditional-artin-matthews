module

public import ArtinMatthews.MarkedPhysicalTypeIIGoodPairing
public import ArtinMatthews.MarkedPhysicalGoodRemovalLog
public import ArtinMatthews.MarkedPhysicalTypeIIHeight
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

/-! The actual scalar endpoint coefficients discharge the good-cutoff
removal estimate on the original full primitive box. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Classical
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

def markedPhysicalTypeIIPairing {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U V : ℝ) (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ) : ℂ :=
  markedPhysicalEdgePairing (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
    ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedPhysicalPrimitiveBox U (16*U) V (2*V))
    (fun _ hz => (Finset.mem_filter.mp hz).2) ψ η d₀ Y Q q
    (fun s => markedPhysicalTypeIIEndpoint e x Sα Sβ modulation β s.1.1.1)
    (fun s => markedPhysicalTypeIIEndpoint e x Sα Sβ modulation β s.1.1.1)

theorem markedPhysicalTypeIIPairing_good_removal
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) {δ : ℝ} (hδ : 0 < δ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (K B etaBound psiBound Qexp C G : ℝ)
    (hK : 0 ≤ K) (hB : 8 ≤ B) (heta : 0 ≤ etaBound) (hpsi : 0 ≤ psiBound)
    (hQexp : 0 ≤ Qexp)
    (hη : ∀ t,‖η t‖ ≤ etaBound) (hψ : ∀ t,‖ψ t‖ ≤ psiBound)
    (hψsupport : Function.support ψ ⊆ Set.Icc (-K) K) :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y U V q : ℝ),x^δ ≤ U → x^δ ≤ V →
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      ∀ (w : ↥(markedPhysicalPrimitiveBox U (16*U) V (2*V)) → ℤ × ℤ),
      (∀ a,markedMinorIntegerDet a.1 (w a)=1) →
      ∀ (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ),
      (∀ n∈Sα,x^δ ≤ (n:ℝ)) → (∀ n∈Sβ,‖β n‖ ≤ (Real.log x)^C) →
      ‖markedPhysicalTypeIIPairing e x ψ η d₀ Y ((Real.log x)^Qexp) q U V Sα Sβ modulation β-
        markedPhysicalTypeIIGoodPairing e x ψ η d₀ Y ((Real.log x)^Qexp) q U V w
          Sα Sβ modulation β‖/(U*V) ≤ (Real.log x)^(-G) := by
  have hsupp : ∀ t,ψ t≠0 → |t| ≤ K := by
    intro t ht
    exact abs_le.mpr (hψsupport ht)
  have hrem := markedPhysical_good_removal_log_saving e he hinj (1/5) B K Qexp 2 C G etaBound psiBound
    (by norm_num) heUpper (by norm_num) (by linarith) hK heta hpsi hδ ψ η hψ hsupp hη
  filter_upwards [hrem,markedPhysicalTypeII_log_height Qexp B (by linarith),
    Real.tendsto_log_atTop.eventually (markedMajorTypeII_supported_alpha δ hδ),
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with x hx hQhi hα hx1 hlog
  intro d₀ Y U V q hU hV hY hYhi w hw Sα Sβ modulation β hSα hβ
  have hUp : 0 < U := (Real.rpow_pos_of_pos (zero_lt_one.trans hx1) δ).trans_le hU
  have hVp : 0 < V := (Real.rpow_pos_of_pos (zero_lt_one.trans hx1) δ).trans_le hV
  have hexp : Real.exp (δ*Real.log x)=x^δ := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hx1),mul_comm]
  have hα' := (hα Sα modulation (fun n hn => hexp.le.trans (hSα n hn))).1
  have hβ' := markedPhysicalRestrictedBeta_bound Sβ β
    (Real.rpow_nonneg (zero_le_one.trans hlog) C) hβ
  have hY1 : 1 ≤ Y := (Real.one_le_exp (Real.rpow_nonneg (zero_le_one.trans hlog) _)).trans hY
  exact hx d₀ Y U V U (16*U) V (2*V) ((Real.log x)^Qexp) q
    (markedPhysicalPrimitiveBox U (16*U) V (2*V)) (fun _ hz => (Finset.mem_filter.mp hz).2) w
    (markedMajorRestrictedCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) modulation Sα)
    (markedPhysicalRestrictedBeta Sβ β) hU hV le_rfl (by linarith) le_rfl le_rfl (by linarith)
    le_rfl (fun _ hz => hz) hw (Real.one_le_rpow hlog hQexp) hQhi le_rfl hY1 hYhi hY
    (by simpa only [Real.rpow_two] using hα') hβ'

end
end ArtinMatthews
