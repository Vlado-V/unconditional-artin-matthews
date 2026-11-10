module

public import ArtinMatthews.SourceComparisonHighTimeTuple
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.SourceComparisonHighTimeCover
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
public import Mathlib.Order.CompletePartialOrder
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

/-! Energy accounting for the subtracted constant, with moderate frequencies
integrated over their whole window and large frequencies on the sparse cover. -/

namespace ArtinMatthews

open Finset Filter MeasureTheory Set

noncomputable section

/-- Reciprocal decay contributes at most (2/S) to the square integral
away from the origin. -/
theorem sourceComparison_reciprocal_square_energy (T S : ℝ) (hS : 0 < S) :
    IntegrableOn (fun t : ℝ => |t|^(-2:ℝ)) (sourceComparisonHighTimes T S) ∧
      (∫ t in sourceComparisonHighTimes T S, |t|^(-2:ℝ)) ≤ 2/S := by
  let f := fun t : ℝ => |t|^(-2:ℝ)
  let D := sourceComparisonHighTimes T S
  have hDcompact : IsCompact D :=
    isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hf : IntegrableOn f D := by
    apply ContinuousOn.integrableOn_compact hDcompact
    exact continuous_abs.continuousOn.rpow_const (fun t ht => Or.inl (hS.trans_le ht.2).ne')
  refine ⟨hf, ?_⟩
  by_cases hST : S ≤ T
  · have hD : D = Icc (-T) (-S) ∪ Icc S T := by
      ext t
      change ((-T ≤ t ∧ t ≤ T) ∧ S ≤ |t|) ↔
        (-T ≤ t ∧ t ≤ -S) ∨ (S ≤ t ∧ t ≤ T)
      constructor
      · rintro ⟨⟨htl, htu⟩, hts⟩
        rcases le_total 0 t with hp | hn
        · exact Or.inr ⟨by simpa only [abs_of_nonneg hp] using hts, htu⟩
        · exact Or.inl ⟨htl, by simpa only [abs_of_nonpos hn, le_neg] using hts⟩
      · rintro (⟨htl, hts⟩ | ⟨hts, htu⟩)
        · exact ⟨⟨htl, by linarith⟩, by rw [abs_of_nonpos (by linarith)]; linarith⟩
        · exact ⟨⟨by linarith, htu⟩, by rwa [abs_of_nonneg (hS.le.trans hts)]⟩
    have hdis : Disjoint (Icc (-T) (-S)) (Icc S T) := by
      apply Set.disjoint_left.mpr
      intro t ht hn
      linarith [ht.2, hn.1]
    have hleft : (∫ t in Icc (-T) (-S), f t) = ∫ t in Icc S T, f t := by
      rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : -T ≤ -S),
        ← intervalIntegral.integral_of_le hST, ← intervalIntegral.integral_comp_neg]
      simp only [f, abs_neg]
    have hright : (∫ t in Icc S T, f t) ≤ 1/S := by
      rw [setIntegral_congr_fun measurableSet_Icc
        (g := fun t : ℝ => t^(-2:ℝ)) (fun t ht => by dsimp [f]; rw [abs_of_pos (hS.trans_le ht.1)]),
        integral_Icc_eq_integral_Ioc]
      calc
        _ ≤ ∫ t in Ioi S, t^(-2:ℝ) := setIntegral_mono_set
          (integrableOn_Ioi_rpow_of_lt (by norm_num) hS)
          (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              exact Real.rpow_nonneg (hS.trans ht).le _)
          (Eventually.of_forall (fun _ ht => ht.1))
        _ = 1/S := by
          rw [integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hS]
          norm_num [Real.rpow_neg_one, one_div]
    have hl : Icc (-T) (-S) ⊆ D := hD.symm ▸ subset_union_left
    have hr : Icc S T ⊆ D := hD.symm ▸ subset_union_right
    change (∫ t in D, f t) ≤ _
    rw [hD, setIntegral_union hdis measurableSet_Icc (hf.mono_set hl) (hf.mono_set hr), hleft]
    exact (add_le_add hright hright).trans_eq (by ring)
  · have hEmpty : D = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact hST (ht.2.trans (abs_le.mpr ht.1))
    change (∫ t in D, f t) ≤ _
    rw [hEmpty, setIntegral_empty]
    positivity

private theorem continuous_square_integrableOn {W : Set ℝ} {T : ℝ}
    (hW : W ⊆ Set.Icc (-T) T) {f : ℝ → ℂ} (hf : Continuous f) :
    IntegrableOn (fun t => ‖f t‖^2) W :=
  (hf.norm.pow 2).integrableOn_Icc.mono_set hW

private theorem norm_add_sq_le_twice (a b : ℂ) :
    ‖a+b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2).trans
    (by nlinarith [sq_nonneg (‖a‖-‖b‖)])

/-- The constant branch is controlled by the model mean square, its
reciprocal moderate decay, its large-time decay, and the literal L² error. -/
theorem sourceComparisonConstant_window_energy (P N Q : ℝ → ℂ) (I : Finset ℤ)
    (T S U ε C m E Eerr : ℝ) (hS : 0 < S) (hε : 0 ≤ ε)
    (hP : Continuous P) (hN : Continuous N) (hQ : Continuous Q)
    (hPb : ∀ t, ‖P t‖ ≤ 2)
    (hcover : ∀ t ∈ Set.Icc (-T) T, ε < ‖P t‖ →
      ∃ z ∈ I, t ∈ Set.Icc (z:ℝ) ((z:ℝ)+1))
    (hmoderate : ∀ t ∈ sourceComparisonHighTimes T S, |t| ≤ U → ‖Q t‖ ≤ C/|t|)
    (hlarge : ∀ t ∈ sourceComparisonHighTimes T S, U < |t| → ‖Q t‖ ≤ m)
    (hmean : (∫ t in Set.Icc (-T) T, ‖N t‖^2) ≤ E)
    (herror : (∫ t in Set.Icc (-T) T, ‖N t-Q t‖^2) ≤ Eerr) :
    (∫ t in sourceComparisonHighTimes T S, ‖P t*N t‖^2) ≤
      16*C^2/S + 4*ε^2*(E+Eerr) + 8*m^2*(I.card:ℝ) + 8*Eerr := by
  let W := sourceComparisonHighTimes T S
  let Wm := W ∩ {t : ℝ | |t| ≤ U}
  let Wl := W ∩ {t : ℝ | U < |t|}
  have hW : W ⊆ Set.Icc (-T) T := inter_subset_left
  have hWmeas := sourceComparisonHighTimes_measurable T S
  have hmmeas : MeasurableSet Wm := hWmeas.inter (isClosed_le continuous_abs continuous_const).measurableSet
  have hlmeas : MeasurableSet Wl := hWmeas.inter (isOpen_lt continuous_const continuous_abs).measurableSet
  have hmW : Wm ⊆ W := inter_subset_left
  have hlW : Wl ⊆ W := inter_subset_left
  have herrCont : Continuous (fun t => N t-Q t) := hN.sub hQ
  have herrorW : (∫ t in W, ‖N t-Q t‖^2) ≤ Eerr :=
    (setIntegral_mono_set (herrCont.norm.pow 2).integrableOn_Icc
      (Eventually.of_forall (fun _ => sq_nonneg _))
      (Eventually.of_forall (fun _ ht => hW ht))).trans herror
  have hmeanW : (∫ t in W, ‖N t‖^2) ≤ E :=
    (setIntegral_mono_set (hN.norm.pow 2).integrableOn_Icc
      (Eventually.of_forall (fun _ => sq_nonneg _))
      (Eventually.of_forall (fun _ ht => hW ht))).trans hmean
  have hmeanQ : (∫ t in W, ‖Q t‖^2) ≤ 2*(E+Eerr) := by
    have hi₁ : IntegrableOn (fun t => 2*‖N t‖^2) W :=
      (continuous_square_integrableOn hW hN).const_mul (2:ℝ)
    have hi₂ : IntegrableOn (fun t => 2*‖N t-Q t‖^2) W :=
      (continuous_square_integrableOn hW herrCont).const_mul (2:ℝ)
    have hc : Continuous (fun t => 2*‖N t‖^2+2*‖N t-Q t‖^2) := by
      fun_prop
    calc
      _ ≤ ∫ t in W, 2*‖N t‖^2+2*‖N t-Q t‖^2 :=
        setIntegral_mono_on (continuous_square_integrableOn hW hQ) (hc.integrableOn_Icc.mono_set hW) hWmeas (fun t _ => by
          have h := norm_add_sq_le_twice (N t) (-(N t-Q t))
          simpa only [show N t + -(N t-Q t) = Q t by ring, norm_neg] using h)
      _ = 2*(∫ t in W, ‖N t‖^2)+2*(∫ t in W, ‖N t-Q t‖^2) := by
        rw [integral_add hi₁ hi₂, integral_const_mul, integral_const_mul]
      _ ≤ _ := by linarith
  have hmid : (∫ t in Wm, ‖P t*Q t‖^2) ≤ 8*C^2/S := by
    obtain ⟨hi,he⟩ := sourceComparison_reciprocal_square_energy T S hS
    calc
      _ ≤ ∫ t in Wm, (4*C^2)*|t|^(-2:ℝ) := by
        apply setIntegral_mono_on (continuous_square_integrableOn (hmW.trans hW) (hP.mul hQ))
          ((hi.mono_set hmW).const_mul _) hmmeas
        intro t ht
        change ‖P t*Q t‖^2 ≤ _
        rw [norm_mul, mul_pow, Real.rpow_neg (abs_nonneg t), Real.rpow_two]
        have h := pow_le_pow_left₀ (norm_nonneg _) (hmoderate t ht.1 ht.2) 2
        rw [div_pow, div_eq_mul_inv] at h
        exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hPb t) 2) h (sq_nonneg _) (by norm_num)).trans_eq
          (by ring)
      _ = 4*C^2*(∫ t in Wm, |t|^(-2:ℝ)) := integral_const_mul _ _
      _ ≤ 4*C^2*(2/S) := mul_le_mul_of_nonneg_left
        ((setIntegral_mono_set hi (Eventually.of_forall (fun _ => by positivity))
          (Eventually.of_forall (fun _ ht => hmW ht))).trans he) (by positivity)
      _ = _ := by ring
  have hlong : (∫ t in Wl, ‖P t*Q t‖^2) ≤ 2*ε^2*(E+Eerr)+4*m^2*(I.card:ℝ) := by
    have hmeanL : (∫ t in Wl, ‖Q t*(1:ℂ)‖^2) ≤ 2*(E+Eerr) := by
      simp only [mul_one]
      exact (setIntegral_mono_set (continuous_square_integrableOn hW hQ)
        (Eventually.of_forall (fun _ => sq_nonneg _))
        (Eventually.of_forall (fun _ ht => hlW ht))).trans hmeanQ
    have hsparse : (∑ z ∈ I, sSup ((fun _t : ℝ => ‖(1:ℂ)‖^2) '' Set.Icc (z:ℝ) ((z:ℝ)+1))) ≤
        (I.card:ℝ) := by
      calc
        _ ≤ ∑ _z ∈ I, (1:ℝ) := by
          apply sum_le_sum
          intro z _
          have hn : (Set.Icc (z:ℝ) ((z:ℝ)+1)).Nonempty :=
            Set.nonempty_Icc.mpr (by linarith)
          rw [Set.Nonempty.image_const hn, csSup_singleton]
          norm_num
        _ = _ := by simp
    have h := sourceComparison_isolated_energy_subset P Q (fun _ => 1) I
      T ε 2 m (2*(E+Eerr)) I.card Wl hlmeas (hlW.trans hW) hP hQ continuous_const
      (fun t _ => hPb t) (fun t ht => hlarge t ht.1 ht.2)
      (fun t ht => hcover t (hW ht.1)) hmeanL hsparse
    simpa only [mul_one, show ε^2*(2*(E+Eerr))+2^2*m^2*(I.card:ℝ) =
      2*ε^2*(E+Eerr)+4*m^2*(I.card:ℝ) by ring] using h
  have hsplit : W = Wm ∪ Wl := by
    ext t
    change t ∈ W ↔ (t ∈ W ∧ |t| ≤ U) ∨ (t ∈ W ∧ U < |t|)
    constructor
    · intro ht
      exact (le_or_gt |t| U).imp (fun h => ⟨ht,h⟩) (fun h => ⟨ht,h⟩)
    · rintro (⟨ht,_⟩ | ⟨ht,_⟩) <;> exact ht
  have hdis : Disjoint Wm Wl := by
    apply Set.disjoint_left.mpr
    intro t hm hl
    exact (not_lt_of_ge (show |t| ≤ U from hm.2)) (show U < |t| from hl.2)
  have hmodel : (∫ t in W, ‖P t*Q t‖^2) ≤
      8*C^2/S + (2*ε^2*(E+Eerr)+4*m^2*(I.card:ℝ)) := by
    conv_lhs => rw [hsplit]
    have hu := setIntegral_union (f := fun t => ‖P t*Q t‖^2) hdis hlmeas
      (continuous_square_integrableOn (hmW.trans hW) (hP.mul hQ))
      (continuous_square_integrableOn (hlW.trans hW) (hP.mul hQ))
    exact hu.trans_le (add_le_add hmid hlong)
  have hi₁ : IntegrableOn (fun t => 2*‖P t*Q t‖^2) W :=
    (continuous_square_integrableOn hW (hP.mul hQ)).const_mul (2:ℝ)
  have hi₂ : IntegrableOn (fun t => 8*‖N t-Q t‖^2) W :=
    (continuous_square_integrableOn hW herrCont).const_mul (8:ℝ)
  have hc : Continuous (fun t => 2*‖P t*Q t‖^2+8*‖N t-Q t‖^2) := by
    fun_prop
  calc
    _ ≤ ∫ t in W, 2*‖P t*Q t‖^2+8*‖N t-Q t‖^2 :=
      setIntegral_mono_on (continuous_square_integrableOn hW (hP.mul hN))
        (hc.integrableOn_Icc.mono_set hW) hWmeas (fun t _ => by
          have h := norm_add_sq_le_twice (P t*Q t) (P t*(N t-Q t))
          change ‖P t*N t‖^2 ≤ _
          rw [show P t*Q t + P t*(N t-Q t) = P t*N t by ring] at h
          have h₂ : ‖P t*(N t-Q t)‖^2 ≤ 4*‖N t-Q t‖^2 := by
            rw [norm_mul, mul_pow]
            simpa only [show (2:ℝ)^2=4 by norm_num] using
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hPb t) 2)
                (sq_nonneg (‖N t-Q t‖))
          exact h.trans (by linarith only [h₂]))
    _ = 2*(∫ t in W, ‖P t*Q t‖^2)+8*(∫ t in W, ‖N t-Q t‖^2) := by
      rw [integral_add hi₁ hi₂, integral_const_mul, integral_const_mul]
    _ ≤ 2*(8*C^2/S + (2*ε^2*(E+Eerr)+4*m^2*(I.card:ℝ)))+8*Eerr :=
      add_le_add (mul_le_mul_of_nonneg_left hmodel (by norm_num))
        (mul_le_mul_of_nonneg_left herrorW (by norm_num))
    _ = _ := by ring

end
end ArtinMatthews
