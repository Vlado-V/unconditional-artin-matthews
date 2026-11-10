module

public import ArtinMatthews.MarkedPhysicalScalarGoodMoment
public import ArtinMatthews.MarkedEstimateActualModel
public import ArtinMatthews.MarkedEstimateMertensBands
public import ArtinMatthews.MarkedPhysicalCappedGlobalActual
public import ArtinMatthews.MarkedPhysicalGoodRemovalLog
public import ArtinMatthews.MarkedPhysicalMomentFromCapped
public import ArtinMatthews.MarkedPhysicalSourceErrorScale
public import ArtinMatthews.MarkedPhysicalTypeIICellBudget
public import ArtinMatthews.MarkedPhysicalTypeIIEndpointDamping
public import ArtinMatthews.MarkedPhysicalTypeIIHeight
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The actual unprojected minor pairing for arbitrary bounded scalar coefficients. -/
namespace ArtinMatthews
open Filter
open scoped Classical BigOperators
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The actual moment and the actual bad-endpoint error apply to both scalar
coefficients using only their global suprema. -/
theorem markedPhysicalScalarPairing_actual_log_saving
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) {δ : ℝ} (hδ : 0 < δ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (K Hexp B W Cα Cβ P : ℝ) (hK : 0 ≤ K) (hHexp : 0 ≤ Hexp) (hB : 8 ≤ B)
    (hW : 0 ≤ W) (hCα : 0 ≤ Cα) (hCβ : 0 ≤ Cβ) (hP : 0 ≤ P)
    (hdepth : 100*(5*(P+2*(Cα+Cβ)+3)+36)<(Fintype.card J:ℝ))
    (hηsupport : Function.support η ⊆ Set.Icc 1 4) (hη : ∀ t,‖η t‖ ≤ 1)
    (hψ : ∀ t,‖ψ t‖ ≤ W) (hψsupport : Function.support ψ ⊆ Set.Icc (-K) K) :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ),0 < d₀ →
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      d₀*Y ≤ Real.exp (Hexp*(Real.log x)^(21/100:ℝ)) →
      ∀ (U V : ℝ),x^δ ≤ U → x^δ ≤ V →
      ∀ α β : ℕ → ℂ, (∀ n,‖α n‖ ≤ (Real.log x)^Cα) → (∀ n,‖β n‖ ≤ (Real.log x)^Cβ) →
      ‖markedPhysicalScalarPairing e x ψ η d₀ Y ((Real.log x)^(P+2*(Cα+Cβ)+12)) 1 U V α β‖ ≤
        (U*V)*(Real.log x)^(-P) := by
  let M := P+2*(Cα+Cβ)+2
  let G := M+1
  let Qexp := G+9
  let F := 32*Real.sqrt (2*(⌈2*K+1⌉₊:ℝ)+1)*(257*Real.exp Hexp)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hG : 0 < G := by dsimp only [G]; positivity
  have hQ : 0 ≤ Qexp := by dsimp only [Qexp]; positivity
  have hQexp : Qexp=P+2*(Cα+Cβ)+12 := by dsimp only [Qexp,G,M]; ring
  have hdepth' : 100*(5*G+36)<(Fintype.card J:ℝ) := by
    dsimp only [G,M]
    linarith
  have he₀ : ∀ j, 0 < e j := fun j => (by norm_num : (0:ℝ)<1/10).trans_le (he j)
  have hbands := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually (he₀ j))
  have hrem := markedPhysical_good_removal_log_saving e he hinj (1/5) B K Qexp Cα Cβ (P+1) 1 W
    (by norm_num) heUpper (by norm_num) (by linarith) hK (by norm_num) hW hδ ψ η hψ
    (fun t ht => abs_le.mpr (hψsupport ht)) hη
  have hcap := markedPhysicalCoordinateCappedGlobal_log_saving e he hinj ψ η hηsupport hη
    (1/2) G B K W (by norm_num) (by norm_num) hG (by linarith) hK hW hdepth' hψ hψsupport
  have hm := markedPhysicalActualPositionMoment_of_capped_bound e he heUpper hinj hδ
    ψ η K Hexp B 1 W Qexp M hK hHexp hB (by norm_num) hW hQ hM hη hψ hψsupport
  filter_upwards [hcap, hm, hrem, hbands, marked_array_disjoint_eventually e hinj,
    markedPhysicalTypeII_log_height Qexp B (by linarith), eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 2 F))]
    with x hc hm hr hb hd hQhi hx hLmax
  intro d₀ Y hd₀ hY hYhi hscale U V hU hV α β hα hβ
  rw [← hQexp]
  let L := Real.log x
  let Q := L^Qexp
  let Z := markedPhysicalPrimitiveBox U (16*U) V (2*V)
  have hZ : ∀ z∈Z,IsCoprime z.1 z.2 := fun _ hz => (Finset.mem_filter.mp hz).2
  let w : Z → ℤ × ℤ := fun z => Classical.choose (markedPrimitivePosition_completion z.1 (hZ z.1 z.2))
  have hw (z : Z) : markedMinorIntegerDet z.1 (w z)=1 :=
    Classical.choose_spec (markedPrimitivePosition_completion z.1 (hZ z.1 z.2))
  have hUp := (Real.rpow_pos_of_pos (zero_lt_one.trans hx) δ).trans_le hU
  have hVp := (Real.rpow_pos_of_pos (zero_lt_one.trans hx) δ).trans_le hV
  have huv := mul_pos hUp hVp
  have hYp := (Real.exp_pos _).trans_le hY
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hLmax
  have hL : 1 ≤ L := (by norm_num : (1:ℝ) ≤ 2).trans hL2
  have hY1 : 1 ≤ Y := (Real.one_le_exp (Real.rpow_nonneg (zero_le_one.trans hL) _)).trans hY
  have hmass (j : J) : 0 < bandReciprocalMass (markedLogPowerBand (e j) x) :=
    (show 0 < Real.log 2/2 by positivity).trans (hb j).1
  let R := markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)
  have hR : 1 ≤ R := markedPhysicalMomentTubeRadius_ge_one _ hK (mul_pos hd₀ hYp).le
  have hmoment := (div_le_iff₀ huv).mp (hm d₀ Y hd₀ hY hYhi hscale (1/2) U V
    (by norm_num) (by norm_num) hU hV (hc d₀ Y hd₀ hY hYhi R hR U V) w hw)
  have hmoment' : markedPhysicalActualPositionMoment e x ψ η d₀ Y Q (1/2) U V w ≤
      (U*V)*L^(-M*(markedMemoryMomentLength x:ℝ)) := by
    exact hmoment.trans_eq (mul_comm _ _)
  let g := markedPhysicalScalarGoodPairing e x ψ η d₀ Y Q (1/2) U V w α β
  let f := markedPhysicalScalarPairing e x ψ η d₀ Y Q (1/2) U V α β
  have hgood := markedPhysicalScalarGoodPairing_moment_bound e x hx hd hmass ψ η d₀ Y Q
    (1/2) K U V Cα Cβ M hd₀ hYp hK hUp hVp hψsupport w α β hα hβ hmoment'
  have hcell := markedPhysicalTypeII_cell_root_bound hL (mul_pos hd₀ hYp).le hHexp hscale
  have hgood' : ‖g‖ ≤ F*(U*V)*L^(-(P+2)) := by
    have heq : 2*(Cα+Cβ)-M = -(P+2) := by dsimp only [M]; ring
    rw [heq] at hgood
    apply hgood.trans
    dsimp only [F]
    gcongr
  have hbad := (div_le_iff₀ huv).mp (hr d₀ Y U V U (16*U) V (2*V) Q (1/2) Z hZ w α β
    hU hV le_rfl (by linarith) le_rfl le_rfl (by linarith) le_rfl (fun _ hz => hz) hw
    (Real.one_le_rpow hL hQ) hQhi le_rfl hY1 hYhi hY hα hβ)
  change ‖f-g‖ ≤ L^(-(P+1))*(U*V) at hbad
  have hF := (le_max_right _ _).trans hLmax
  have hgpow : F*L^(-(P+2)) ≤ L^(-(P+1)) := by
    simpa only [Nat.cast_one,mul_one,show P+1+1=P+2 by ring] using
      (markedPhysicalSourceErrorScale (N:=1) (G:=P+1) hL hF (by norm_num))
  have hp : 2*L^(-(P+1)) ≤ L^(-P) := by
    simpa only [Nat.cast_one,mul_one] using
      (markedPhysicalSourceErrorScale (N:=1) (G:=P) hL hL2 (by norm_num))
  have heq : f = markedPhysicalScalarPairing e x ψ η d₀ Y Q 1 U V α β :=
    markedPhysicalEdgePairing_endpoint_damping (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) _ ⌊L^(1/100:ℝ)⌋₊ Z hZ ψ η d₀ Y Q (1/2) α β
  rw [← heq]
  calc
    _ ≤ ‖f-g‖+‖g‖ := by simpa only [sub_add_cancel] using norm_add_le (f-g) g
    _ ≤ (U*V)*(2*L^(-(P+1))) := by
      have hh := mul_le_mul_of_nonneg_left hgpow huv.le
      linarith [hgood']
    _ ≤ _ := mul_le_mul_of_nonneg_left hp huv.le

end
end ArtinMatthews
