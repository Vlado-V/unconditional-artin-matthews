module

public import ArtinMatthews.SourceComparisonDyads
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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

/-! The occupied dyads inherit the actual small- and giant-prime scales. -/

namespace ArtinMatthews

open Finset Filter
open scoped Topology

noncomputable section

theorem sourceComparisonDyadScale_one_le (j : ℕ) : (1:ℝ) ≤ sourceComparisonDyadScale j := by
  exact_mod_cast Nat.succ_le_of_lt (show 0 < sourceComparisonDyadScale j by
    unfold sourceComparisonDyadScale
    positivity)

theorem sourceComparisonSmallDyad_scales :
    ∀ᶠ X : ℝ in atTop, ∀ (S : Finset ℕ) (j : ℕ),
      (∀ p ∈ S, p.Prime ∧ Real.exp (X^(28/100:ℝ)) ≤ (p:ℝ) ∧
        (p:ℝ) ≤ Real.exp (X^(36/100:ℝ))) →
      j ∈ sourceComparisonDyadIndices S →
      let P : ℝ := sourceComparisonDyadScale j
      1 < P ∧ (1/2)*X^(1/10:ℝ) ≤ Real.log P ∧ Real.log P ≤ X ∧
        P ≤ Real.exp (X^(36/100:ℝ)) := by
  have hscale := tendsto_rpow_atTop (show (0:ℝ) < 28/100 by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    hscale.eventually (eventually_ge_atTop (2*Real.log 2))] with X hX hlog2
  intro S j hS hj
  obtain ⟨p,hp,hpj⟩ := mem_image.mp hj
  obtain ⟨hpp,hplo,hphi⟩ := hS p hp
  have hd : p ∈ sourceComparisonDyad S j := mem_filter.mpr ⟨hp,hpj⟩
  obtain ⟨hl,hu⟩ := sourceComparisonDyad_bounds hd hpp.pos
  let P : ℝ := sourceComparisonDyadScale j
  have hP1 : 1 ≤ P := sourceComparisonDyadScale_one_le _
  have hP0 : 0 < P := zero_lt_one.trans_le hP1
  have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
  have hPcap : P ≤ Real.exp (X^(36/100:ℝ)) :=
    (show P ≤ p by dsimp [P]; exact_mod_cast hl).trans hphi
  have hlo : X^(28/100:ℝ) ≤ Real.log (p:ℝ) := (Real.le_log_iff_exp_le hp0).mpr hplo
  have hhi : Real.log (p:ℝ) ≤ Real.log 2+Real.log P := by
    rw [← Real.log_mul (by norm_num) hP0.ne']
    exact Real.log_le_log hp0 (by dsimp [P]; exact_mod_cast hu)
  have hlpow : X^(1/10:ℝ) ≤ X^(28/100:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
  have hlower : (1/2)*X^(1/10:ℝ) ≤ Real.log P := by linarith
  have hP : 1 < P := (Real.log_pos_iff hP0.le).mp ((by positivity : 0 < (1/2)*X^(1/10:ℝ)).trans_le hlower)
  have hlogP : Real.log P ≤ X := by
    have h := (Real.log_le_iff_le_exp hP0).mpr hPcap
    exact h.trans (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (36/100:ℝ) ≤ 1))
  exact ⟨hP, hlower, hlogP, hPcap⟩

theorem sourceComparisonGiantDyad_scales (ε a : ℝ) (hε : 0 < ε) (hεq : ε < 1/4) :
    ∀ᶠ X : ℝ in atTop, ∀ (j : ℕ),
      j ∈ sourceComparisonDyadIndices (giantPrimeWindow (Real.exp X) ε) →
      let H : ℝ := sourceComparisonDyadScale j
      let u := max H ((Real.exp X)^(1-ε))
      let v := min (2*H) ((Real.exp X)^(1-ε/2))
      0 < j ∧ Real.exp ((1-2*ε)*X) ≤ H ∧ H ≤ u ∧ u ≤ v ∧ v ≤ 2*H ∧
        v ≤ Real.exp ((1-ε/2)*X) ∧ H ≤ Real.exp ((1-ε/2)*X) ∧
        ∀ q : ℕ, ∀ [NeZero q], (q:ℝ) ≤ X^a →
          ∀ p ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime, IsUnit (p:ZMod q) := by
  let τ := 1-2*ε
  have hτ : 0 < τ := by dsimp [τ]; linarith
  have hscale : Tendsto (fun X : ℝ => Real.exp (ε*X)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hε)
  have hlim := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a τ hτ
  filter_upwards [eventually_ge_atTop (1:ℝ), hscale.eventually (eventually_ge_atTop (2:ℝ)),
    hlim.eventually (gt_mem_nhds zero_lt_one)] with X hX h2 hqX
  intro j hj
  let H : ℝ := sourceComparisonDyadScale j
  let u := max H ((Real.exp X)^(1-ε))
  let v := min (2*H) ((Real.exp X)^(1-ε/2))
  obtain ⟨p,hp,hpj⟩ := mem_image.mp hj
  obtain ⟨hprime,hplo,hphi⟩ := (mem_giantPrimeWindow (Real.exp_pos X).le).mp hp
  have hd : p ∈ sourceComparisonDyad (giantPrimeWindow (Real.exp X) ε) j :=
    mem_filter.mpr ⟨hp,hpj⟩
  obtain ⟨hl,hu⟩ := sourceComparisonDyad_bounds hd hprime.pos
  have he (s : ℝ) : (Real.exp X)^s = Real.exp (s*X) := by
    rw [← Real.exp_mul, mul_comm]
  simp only [he] at hplo hphi
  have hHlo : Real.exp (τ*X) ≤ H := by
    have hp2 : (p:ℝ) ≤ 2*H := by dsimp [H]; exact_mod_cast hu
    have hx : 2*Real.exp (τ*X) ≤ (p:ℝ) := by
      calc
        _ ≤ Real.exp (ε*X)*Real.exp (τ*X) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
        _ = Real.exp ((1-ε)*X) := by rw [← Real.exp_add]; congr 1; dsimp [τ]; ring
        _ ≤ _ := hplo.le
    linarith
  have hj₀ : 0 < j := by
    by_contra h
    have hz : j = 0 := by omega
    have hH1 : H = 1 := by simp [H, sourceComparisonDyadScale, hz]
    have hh := Real.one_lt_exp_iff.mpr (mul_pos hτ (by linarith : 0 < X))
    linarith
  have hpH : H < (p:ℝ) := by
    dsimp [H]
    exact_mod_cast ((sourceComparisonDyad_mem_iff hj₀).mp hd).2.1
  have huv : u ≤ v := by
    have hpu : u < (p:ℝ) := max_lt_iff.mpr ⟨hpH, by rwa [he]⟩
    have hpv : (p:ℝ) ≤ v := le_min (by dsimp [H]; exact_mod_cast hu) (by rwa [he])
    exact hpu.le.trans hpv
  refine ⟨hj₀, hHlo, le_max_left _ _, huv, min_le_left _ _,
    (min_le_right _ _).trans_eq (he _), (show H ≤ p by dsimp [H]; exact_mod_cast hl).trans hphi, ?_⟩
  intro q _ hq n hn
  have hqp : (q:ℝ) ≤ H := by
    apply hq.trans
    have hh : X^a*Real.exp (-τ*X) ≤ 1 := hqX.le
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv] at hh
    exact ((div_le_one (Real.exp_pos _)).mp hh).trans hHlo
  have hnu : u < (n:ℝ) := Nat.lt_of_floor_lt (mem_Ioc.mp (mem_filter.mp hn).1).1
  have hqn : q < n := by exact_mod_cast hqp.trans_lt ((le_max_left _ _).trans_lt hnu)
  have hnp : n.Prime := (mem_filter.mp hn).2
  have hcop : n.Coprime q := hnp.coprime_iff_not_dvd.mpr
    (fun hd => (not_le_of_gt hqn) (Nat.le_of_dvd (NeZero.pos q) hd))
  exact ⟨ZMod.unitOfCoprime n hcop, ZMod.coe_unitOfCoprime _ _⟩

end
end ArtinMatthews
