module

public import ArtinMatthews.MarkedPhysicalPadCollisionMass
public import ArtinMatthews.MarkedBonferroniTail
public import ArtinMatthews.MarkedEstimateMertensBands
public import ArtinMatthews.MarkedTypeIICollisionDecay
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual auxiliary pads have length floor(log(x)^.01), one less
than the physical active lists. Their repeated/forbidden collision mass
saves every fixed logarithmic power uniformly in both unshared tuples.
The separate unshared-label diagonal is not included in this estimate. -/

namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators Topology

theorem markedPhysicalAuxiliaryPad_count_bound {x : ℝ} (hlog : 1 ≤ Real.log x) :
    let M := ⌊(Real.log x)^(1/100:ℝ)⌋₊
    (M:ℝ)^2 + 2*(M:ℝ) ≤ 3*(Real.log x)^(1/50:ℝ) := by
  let S := (Real.log x)^(1/100:ℝ)
  let M := ⌊S⌋₊
  change (M:ℝ)^2 + 2*(M:ℝ) ≤ 3*(Real.log x)^(1/50:ℝ)
  have hL : 0 < Real.log x := zero_lt_one.trans_le hlog
  have hS : 1 ≤ S := Real.one_le_rpow hlog (by norm_num)
  have hM : (M:ℝ) ≤ S := Nat.floor_le (zero_le_one.trans hS)
  have hM2 : (M:ℝ)^2 ≤ S^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hM 2
  have hS2 : S^2 = (Real.log x)^(1/50:ℝ) := by
    dsimp only [S]
    rw [← Real.rpow_mul_natCast hL.le]
    norm_num
  calc
    _ ≤ S^2 + 2*S := by linarith
    _ ≤ 3*S^2 := by nlinarith [mul_nonneg (show 0 ≤ S by linarith) (show 0 ≤ S-1 by linarith)]
    _ = _ := by rw [hS2]

variable {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ)

theorem markedPhysicalActualPadCollision_le
    (he : ∀ j, (1/10:ℝ) ≤ e j) {x : ℝ} (hlog : 1 ≤ Real.log x)
    (hV : ∀ j, Real.log 2/2 ≤ bandReciprocalMass (markedLogPowerBand (e j) x))
    (b a : (j : J) → ↥(markedLogPowerBand (e j) x)) :
    markedPhysicalPadCollisionMass (fun j => markedLogPowerBand (e j) x)
        ⌊(Real.log x)^(1/100:ℝ)⌋₊ b a ≤
      (6*(Fintype.card J:ℝ)/Real.log 2)*(Real.log x)^(1/50:ℝ)*
        Real.exp (-(Real.log x)^(1/10:ℝ)) := by
  let P := fun j => markedLogPowerBand (e j) x
  let L := Real.log x
  let M := ⌊L^(1/100:ℝ)⌋₊
  let E := Real.exp (L^(1/10:ℝ))
  have hL : 0 < L := zero_lt_one.trans_le hlog
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hE : 0 < E := Real.exp_pos _
  have hVpos (j : J) : 0 < bandReciprocalMass (P j) :=
    (div_pos hlog₂ (by norm_num)).trans_le (hV j)
  have hb := markedPhysicalPadCollisionMass_finite_bound P M hVpos
    (fun _ => E) (fun _ => hE)
    (fun j _ hp => marked_band_common_lower (he j) hlog hp) b a
  have hcount : (M:ℝ)^2+2*(M:ℝ) ≤ 3*L^(1/50:ℝ) :=
    markedPhysicalAuxiliaryPad_count_bound hlog
  have hatom (j : J) : 1/(E*bandReciprocalMass (P j)) ≤
      (2/Real.log 2)*Real.exp (-L^(1/10:ℝ)) := by
    calc
      _ ≤ 1/(E*(Real.log 2/2)) :=
        one_div_le_one_div_of_le (mul_pos hE (div_pos hlog₂ (by norm_num)))
          (mul_le_mul_of_nonneg_left (hV j) hE.le)
      _ = _ := by
        dsimp only [E]
        rw [Real.exp_neg]
        field_simp
  have hs : (∑ j, 1/(E*bandReciprocalMass (P j))) ≤
      (Fintype.card J:ℝ)*((2/Real.log 2)*Real.exp (-L^(1/10:ℝ))) := by
    calc
      _ ≤ ∑ _j : J, (2/Real.log 2)*Real.exp (-L^(1/10:ℝ)) :=
        Finset.sum_le_sum (fun j _ => hatom j)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change markedPhysicalPadCollisionMass P M b a ≤ _
  apply hb.trans
  calc
    _ ≤ (3*L^(1/50:ℝ))*((Fintype.card J:ℝ)*((2/Real.log 2)*Real.exp (-L^(1/10:ℝ)))) :=
      mul_le_mul hcount hs
        (Finset.sum_nonneg (fun j _ => one_div_nonneg.mpr (mul_nonneg hE.le (hVpos j).le)))
        (by positivity)
    _ = _ := by ring

theorem markedPhysicalActualPadCollision_log_saving
    (he : ∀ j, (1/10:ℝ) ≤ e j) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ b a : (j : J) → ↥(markedLogPowerBand (e j) x),
      markedPhysicalPadCollisionMass (fun j => markedLogPowerBand (e j) x)
        ⌊(Real.log x)^(1/100:ℝ)⌋₊ b a ≤ (Real.log x)^(-A) := by
  let C := 6*(Fintype.card J:ℝ)/Real.log 2
  have hV := eventually_all.mpr (fun j : J => marked_log_power_band_mass_eventually
    ((by norm_num : (0:ℝ) < 1/10).trans_le (he j)))
  have hdecay := ((rpow_mul_exp_neg_rpow_tendsto (A+1/50)
    (by norm_num : (0:ℝ) < 1/10) (by norm_num : (0:ℝ) < 1)).comp
      Real.tendsto_log_atTop).const_mul C
  simp only [Function.comp_def, neg_mul, one_mul, mul_zero] at hdecay
  have hsmall : ∀ᶠ x : ℝ in atTop,
      C*((Real.log x)^(A+1/50)*Real.exp (-(Real.log x)^(1/10:ℝ))) ≤ 1 :=
    ((tendsto_order.1 hdecay).2 1 zero_lt_one).mono (fun _ hx => hx.le)
  filter_upwards [hV, Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)), hsmall]
    with x hxV hlog hxsmall
  intro b a
  let L := Real.log x
  let m := markedPhysicalPadCollisionMass (fun j => markedLogPowerBand (e j) x)
    ⌊L^(1/100:ℝ)⌋₊ b a
  have hL : 0 < L := zero_lt_one.trans_le hlog
  have hb : m ≤ C*L^(1/50:ℝ)*Real.exp (-L^(1/10:ℝ)) :=
    markedPhysicalActualPadCollision_le e he hlog (fun j => (hxV j).1.le) b a
  have hw : L^A*m ≤ 1 := by
    apply (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hL.le _)).trans
    calc
      _ = C*(L^(A+1/50)*Real.exp (-L^(1/10:ℝ))) := by rw [Real.rpow_add hL]; ring
      _ ≤ _ := hxsmall
  change m ≤ L^(-A)
  calc
    _ ≤ 1/L^A := (le_div_iff₀ (Real.rpow_pos_of_pos hL A)).mpr (by simpa only [mul_comm] using hw)
    _ = _ := by rw [Real.rpow_neg hL.le, one_div]

end
end ArtinMatthews
