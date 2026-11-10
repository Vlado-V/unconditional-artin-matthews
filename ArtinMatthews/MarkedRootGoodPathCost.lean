module

public import ArtinMatthews.MarkedRootGoodPathCells
public import ArtinMatthews.MarkedRawGoodCutComplexity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The actual full first/beta path boundary cost has an explicit
sublinear-logarithmic envelope from prime, slot, path-height and length data. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

def markedRootGoodPathCostExponent (K : ℕ) (B : ℝ) : ℝ :=
  (40960+30*(18*(1+(2:ℝ)^K*(K:ℝ))+1))+2*B+6*(10*((K:ℝ)+1)+B+64)

theorem markedRootGoodPathBoundaryCost_nonneg {J ι : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ} (I : Finset ι)
    (source : ι → MarkedRawActive (markedRawActualPrimeBand e x) M)
    (d₀ Y H : ℝ) (z w : ι → Fin 2 → ℝ) (hH : 0 ≤ H) :
    0 ≤ markedRootGoodPathBoundaryCost e x I source d₀ Y H z w := by
  exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hH)
    (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)))

theorem markedRootGoodPathCost_envelope {J ι : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) {β B α x : ℝ} (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hβα : β+(1/100:ℝ) ≤ α) (hα : (1/5:ℝ) ≤ α)
    (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ β)
    (I : Finset ι) (source : ι → MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
    (d₀ Y H : ℝ) (hY : 1 ≤ Y) (hYhi : Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)))
    (hH : 0 ≤ H) (hHhi : H ≤ Real.exp (B*(Real.log x)^α))
    (hI : (I.card:ℝ) ≤ Real.exp (B*(Real.log x)^α)) (z w : ι → Fin 2 → ℝ) :
    markedRootGoodPathBoundaryCost e x I source d₀ Y H z w ≤
      Real.exp (markedRootGoodPathCostExponent (Fintype.card J) B*(Real.log x)^α) := by
  let t := (Real.log x)^α
  let C : ℝ := 18*(1+(2:ℝ)^(Fintype.card J)*(Fintype.card J:ℝ))+1
  let D : ℝ := 10*((Fintype.card J:ℝ)+1)+B+64
  let L : ℝ := 40960+30*C
  have ht : 1 ≤ t := Real.one_le_rpow hlog (by linarith)
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have h64 : (64:ℝ) ≤ Real.exp (64*t) := by linarith [Real.add_one_le_exp (64*t)]
  have hRA : 64*H ≤ markedRawRootArcEnvelope (Fintype.card J) (B+64) α x := by
    calc
      _ ≤ Real.exp (64*t)*Real.exp (B*t) := mul_le_mul h64 hHhi hH (Real.exp_pos _).le
      _ = Real.exp ((B+64)*t) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        change (B+64)*t ≤ (10*((Fintype.card J:ℝ)+1)+(B+64))*t
        have hk : 0 ≤ (Fintype.card J:ℝ) := Nat.cast_nonneg _
        nlinarith
  have hy' : Y ≤ Real.exp ((B+64)*(Real.log x)^(1/5:ℝ)) := hYhi.trans
    (Real.exp_le_exp.mpr (by have hp := Real.rpow_nonneg (zero_le_one.trans hlog) (1/5:ℝ); nlinarith))
  have hc (k : ι) :
      ((markedTransportedRatioAllCuts (z k) (w k) (markedRawGoodArcLevels e x (source k) d₀ Y (64*H))).card:ℝ) ≤
      C*Real.exp (6*D*t) := by
    apply (markedRawGood_allCuts_card_envelope e hβ (by linarith : 0 ≤ B+64) hβα hα hlog he
      (source k) d₀ Y (64*H) hY hy' (by positivity) hRA (z k) (w k)).trans_eq
    unfold markedRawRootArcEnvelope
    rw [← Real.exp_nat_mul]
    congr 2
    dsimp [D,t]
    ring
  have hf : 40960*(I.card:ℝ)*H ≤ 40960*Real.exp (2*B*t) := by
    calc
      _ ≤ 40960*Real.exp (B*t)*Real.exp (B*t) := by gcongr
      _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; ring
  have hs : 30*(∑ k ∈ I,((markedTransportedRatioAllCuts (z k) (w k)
      (markedRawGoodArcLevels e x (source k) d₀ Y (64*H))).card:ℝ)) ≤
      30*C*Real.exp ((B+6*D)*t) := by
    calc
      _ ≤ 30*∑ _k ∈ I,C*Real.exp (6*D*t) := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun k _ => hc k)) (by norm_num)
      _ = 30*(I.card:ℝ)*(C*Real.exp (6*D*t)) := by rw [Finset.sum_const,nsmul_eq_mul]; ring
      _ ≤ 30*Real.exp (B*t)*(C*Real.exp (6*D*t)) := by gcongr
      _ = _ := by
        rw [show 30*Real.exp (B*t)*(C*Real.exp (6*D*t)) = 30*C*(Real.exp (B*t)*Real.exp (6*D*t)) by ring,
          ← Real.exp_add]
        congr 2
        ring
  have hfirst : Real.exp (2*B*t) ≤ Real.exp ((2*B+6*D)*t) := Real.exp_le_exp.mpr (by nlinarith)
  have hsecond : Real.exp ((B+6*D)*t) ≤ Real.exp ((2*B+6*D)*t) := Real.exp_le_exp.mpr (by nlinarith)
  have hlead : L ≤ Real.exp (L*t) := by
    apply (show L ≤ Real.exp L by linarith [Real.add_one_le_exp L]).trans
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc
    _ ≤ 40960*Real.exp (2*B*t)+30*C*Real.exp ((B+6*D)*t) := add_le_add hf hs
    _ ≤ 40960*Real.exp ((2*B+6*D)*t)+30*C*Real.exp ((2*B+6*D)*t) := by gcongr
    _ = L*Real.exp ((2*B+6*D)*t) := by dsimp [L]; ring
    _ ≤ Real.exp (L*t)*Real.exp ((2*B+6*D)*t) := mul_le_mul_of_nonneg_right hlead (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      dsimp [markedRootGoodPathCostExponent,L,C,D,t]
      ring

end ArtinMatthews
