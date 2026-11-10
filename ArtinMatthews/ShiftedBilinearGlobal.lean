module

public import ArtinMatthews.ShiftedABLLevelRemoval
public import ArtinMatthews.ShiftedRawDyadicTarget
public import ArtinMatthews.ShiftedBilinearDyadic
public import ArtinMatthews.ShiftedBilinearDyadicLog
public import ArtinMatthews.ShiftedBilinearScale
public import ArtinMatthews.ShiftedPhiDyadic
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

namespace ArtinMatthews
open Set OAI.SevenEighths
open scoped BigOperators ContDiff
noncomputable section

theorem giantSamplingCoprimeShiftedBilinearBound_of_dyadic
    (N : ℕ) (η : HeckeFamily.Character) (Φ : ℝ → ℝ)
    (hΦ : ContDiff ℝ ∞ Φ) (hsupp : Function.support Φ ⊆ Icc (1 : ℝ) 2)
    (hraw : ∀ ν : ℝ, 0 < ν → ∃ C : ℝ, 0 < C ∧ ShiftedRawDyadicBound N η ν C) :
    ∀ ν : ℝ, 0 < ν → ∃ Cν : ℝ, 0 < Cν ∧ ∀ x : ℝ, 1 ≤ x →
      GiantSamplingCoprimeShiftedBilinearBound N η Φ x ν Cν := by
  obtain ⟨CΦ, hCΦ, hphi⟩ := giantCubicSamplingBilinear_phi_dyadic Φ hΦ hsupp
  intro ν hν
  let δ := ν / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  obtain ⟨Cr, hCr, hrawδ⟩ := hraw δ hδ
  obtain ⟨Clog, hClog, hlog⟩ := shiftedBilinear_dyadic_log_square_le_rpow δ hδ
  let Cbase : ℝ := CΦ * Cr * (4 * (2 : ℝ) ^ δ)
  let Cν : ℝ := Cbase * Clog
  have hCbase : 0 < Cbase := by dsimp only [Cbase]; positivity
  refine ⟨Cν, mul_pos hCbase hClog, ?_⟩
  intro x hx lo hi hlo hlohi A B α β hA hcop hB hα hβ
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  let Q : ℝ := x * lo ^ (-(1 / 2) : ℝ) + x ^ (7 / 8 : ℝ) * hi ^ (3 / 8 : ℝ)
  have hlo0 : 0 ≤ lo := zero_le_one.trans hlo
  have hhi0 : 0 ≤ hi := hlo0.trans hlohi
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  let D := shiftedBilinearDyadicIndices x
  let W : ℝ := Cbase * x ^ δ * Q
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hblock (k l : ℕ) :
      ‖giantCubicSamplingBilinear η Φ x (shiftedBilinearDyadicBlock x A k)
        (shiftedBilinearDyadicBlock x B l) α β‖ ≤ W := by
    let Ak := shiftedBilinearDyadicBlock x A k
    let Bl := shiftedBilinearDyadicBlock x B l
    by_cases hactive : ∃ m ∈ Ak, ∃ n ∈ Bl, Φ (((m * n : ℕ) : ℝ) / x) ≠ 0
    · obtain ⟨m, hm, n, hn, htest⟩ := hactive
      have hrow (m : ℕ) (hm : m ∈ A) : lo ≤ (m : ℝ) ∧ (m : ℝ) ≤ hi :=
        (hA m hm).2
      have hgeometry := shiftedBilinearDyadicBlock_active_bounds hx0 hsupp hrow hm hn htest
      have hM : 0 < (2 : ℕ) ^ k := by positivity
      have hT : 0 < (2 : ℕ) ^ l := by positivity
      have hAk : Ak ⊆ Finset.Icc (2 ^ k) (2 * 2 ^ k) := by
        intro a ha
        have h := shiftedBilinearDyadicBlock_bounds ha
        exact Finset.mem_Icc.mpr ⟨h.1, h.2.le⟩
      have hBl : Bl ⊆ Finset.Icc (2 ^ l) (2 * 2 ^ l) := by
        intro b hb
        have h := shiftedBilinearDyadicBlock_bounds hb
        exact Finset.mem_Icc.mpr ⟨h.1, h.2.le⟩
      have hsf (a : ℕ) (ha : a ∈ Ak) : Squarefree a :=
        (hA a (shiftedBilinearDyadicBlock_subset x A k ha)).1
      have hcp (a : ℕ) (ha : a ∈ Ak) : N.Coprime a :=
        (hcop a (shiftedBilinearDyadicBlock_subset x A k ha)).symm
      have ha (a : ℕ) (ha : a ∈ Ak) : ‖α a‖ ≤ 1 :=
        hα a (shiftedBilinearDyadicBlock_subset x A k ha)
      have hb (b : ℕ) (hb : b ∈ Bl) : ‖β b‖ ≤ 1 :=
        hβ b (shiftedBilinearDyadicBlock_subset x B l hb)
      have hbound := hphi N η δ Cr hCr.le hrawδ x hx0 (2 ^ k) (2 ^ l) hM hT
        Ak Bl hAk hBl hsf hcp α β ha hb
      have hscale := shiftedBilinear_dyadic_scale
        (by exact_mod_cast hM : 0 < ((2 ^ k : ℕ) : ℝ))
        (by exact_mod_cast hT : 0 < ((2 ^ l : ℕ) : ℝ))
        hx hlo hgeometry.2.2.2 hgeometry.2.2.1 hgeometry.1 hδ.le
      calc
        _ ≤ CΦ * Cr * ((((2 ^ k : ℕ) : ℝ) * ((2 ^ l : ℕ) : ℝ)) ^ δ) *
            (Real.sqrt ((2 ^ k : ℕ) : ℝ) * ((2 ^ l : ℕ) : ℝ) +
              ((2 ^ k : ℕ) : ℝ) ^ (5 / 4 : ℝ) * ((2 ^ l : ℕ) : ℝ) ^ (7 / 8 : ℝ)) := hbound
        _ ≤ CΦ * Cr * ((4 * (2 : ℝ) ^ δ) * x ^ δ * Q) := by
          simpa only [Q, mul_assoc, neg_div] using mul_le_mul_of_nonneg_left hscale (mul_pos hCΦ hCr).le
        _ = W := by dsimp only [W, Cbase]; ring
    · rw [giantCubicSamplingBilinear_eq_zero_of_no_active η Φ x Ak Bl α β hactive, norm_zero]
      exact hW
  have hcount := shiftedBilinearDyadicIndices_count_le hx0.le
  have hcount2 : ((D.card : ℝ) ^ 2) ≤ Clog * x ^ δ := by
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hcount 2).trans (hlog x hx)
  change ‖giantCubicSamplingBilinear η Φ x A B α β‖ ≤ Cν * x ^ ν * Q
  calc
    _ = ‖∑ k ∈ D, ∑ l ∈ D, giantCubicSamplingBilinear η Φ x
        (shiftedBilinearDyadicBlock x A k) (shiftedBilinearDyadicBlock x B l) α β‖ := by
      rw [giantCubicSamplingBilinear_eq_dyadic η Φ x A B α β hx0 hsupp]
    _ ≤ ∑ k ∈ D, ∑ l ∈ D, ‖giantCubicSamplingBilinear η Φ x
        (shiftedBilinearDyadicBlock x A k) (shiftedBilinearDyadicBlock x B l) α β‖ :=
      (norm_sum_le D _).trans (Finset.sum_le_sum (fun k hk => norm_sum_le D _))
    _ ≤ ∑ k ∈ D, ∑ l ∈ D, W :=
      Finset.sum_le_sum (fun k hk => Finset.sum_le_sum (fun l hl => hblock k l))
    _ = (D.card : ℝ) ^ 2 * W := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ (Clog * x ^ δ) * W := mul_le_mul_of_nonneg_right hcount2 hW
    _ = Cν * x ^ ν * Q := by
      have hνδ : ν = δ + δ := by dsimp only [δ]; ring
      rw [hνδ, Real.rpow_add hx0]
      dsimp only [Cν, W]
      ring

end
end ArtinMatthews
