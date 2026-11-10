module

public import ArtinMatthews.MarkedMajorFourierWeight
public import ArtinMatthews.MarkedMajorLabelMean
public import ArtinMatthews.MarkedMajorLabelBounded
public import ArtinMatthews.MarkedMajorLabelLocalMean
public import ArtinMatthews.MarkedMajorMellinLocalMeanTail
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

/-! Actual weighted coarse means at every enlarged scale W*H*U.
The sole loss is linear in W, uniformly for all W ≥ 1. -/
namespace ArtinMatthews
open Finset Filter MeasureTheory
open scoped Topology

theorem marked_major_label_weighted_scaled_mean (σ D B : ℝ) (hσ : 0 ≤ σ) (hB : 0 ≤ B)
    (cutoff : ℝ → ℂ) (hcutoff : ∀ y,‖cutoff y‖ ≤ 1)
    (hsupp : Function.support cutoff ⊆ Set.Iic B) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ L : ℝ in atTop,∀ {J : Type} [Fintype J]
      (bands : J → Finset ℕ),
      (∀ j p,p ∈ bands j → p.Prime) →
      Pairwise (fun i j => Disjoint (bands i) (bands j)) →
      (∀ j,0 < bandReciprocalMass (bands j)) →
      ∀ (Y θ H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ),
      0 < Y → 0 < H → 0 < U → 1 ≤ H*U → H*U ≤ Real.exp (σ*L) →
      H ≤ u → v ≤ 2*H → 1 ≤ Real.log u → U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
      (∀ n ∈ Icc l r,‖β n‖ ≤ L^D) →
      ∀ (k q : ℕ) (χb : DirichletCharacter ℂ k) (χ : DirichletCharacter ℂ q) (modulation c scale : ℝ), 1 ≤ scale →
      ∀ n : ℕ, 2 ≤ n →
      (∫ t : ℝ,markedMajorFourierWeight (scale*(H*U)) n (t-c)*
        ‖markedMajorLabelEndpoint bands cutoff χb θ Y χ (Real.exp (L^(6/25:ℝ))) modulation H u v U l r β t‖^2) ≤
          C*scale*L^(2*D+5) := by
  obtain ⟨C,hC,hmean⟩ := marked_major_label_translated_mean σ D B hσ hB cutoff hcutoff hsupp
  refine ⟨markedMajorLocalMeanConstant*(3*C/2),mul_pos markedMajorLocalMeanConstant_pos (by positivity),?_⟩
  filter_upwards [hmean,eventually_ge_atTop (1:ℝ)] with L hL hLone
  intro J _ bands hbands hdis hV Y θ H u v U l r β hY hH hU hX hXupper hHu hv hlog hl hr hβ
    k q χb χ modulation c scale hscale
  let W : ℝ := Real.exp (L^(6/25:ℝ))
  let Q := markedMajorLabelEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β
  have hQc : Continuous Q := markedMajorLabelEndpoint_continuous bands cutoff χb θ Y χ W modulation H u v U l r β
  obtain ⟨K,hK⟩ := markedMajorLabelEndpoint_bounded bands cutoff χb θ Y χ W modulation H u v U l r β
  have hscale0 : 0 < scale := zero_lt_one.trans_le hscale
  have hlocal (z : ℝ) :
      (∫ t in Set.Icc z (z+scale*(H*U)), ‖Q t‖^2) ≤ (3*C/2)*scale*L^(2*D+5) := by
    rw [markedMajor_local_integral_eq_translated _ z (scale*(H*U)) (by positivity)]
    have h := hL bands hbands hdis hV Y θ H u v U (scale*(H*U)/2)
      (z+scale*(H*U)/2) l r β hY hH hU (by positivity) hX hXupper hHu hv hlog hl hr hβ
      k q χb χ modulation
    have he : 1+(scale*(H*U)/2)/(H*U) = 1+scale/2 := by field_simp
    rw [he] at h
    apply h.trans
    have hLp : 0 ≤ C*L^(2*D+5) := by positivity
    calc
      _ ≤ C*L^(2*D+5)*(3*scale/2) := mul_le_mul_of_nonneg_left (by linarith) hLp
      _ = _ := by ring
  have hM : 0 ≤ (3*C/2)*scale*L^(2*D+5) := by positivity
  intro n hn
  have h := markedMajorLocalMean_weighted_higher Q hQc K hK (mul_pos hscale0 (mul_pos hH hU)) hM hlocal c hn
  simpa only [Q,W,mul_assoc] using h

theorem marked_major_label_weighted_scaled_tail (σ D B : ℝ) (hσ : 0 ≤ σ) (hB : 0 ≤ B)
    (cutoff : ℝ → ℂ) (hcutoff : ∀ y,‖cutoff y‖ ≤ 1)
    (hsupp : Function.support cutoff ⊆ Set.Iic B) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ L : ℝ in atTop,∀ {J : Type} [Fintype J]
      (bands : J → Finset ℕ),
      (∀ j p,p ∈ bands j → p.Prime) →
      Pairwise (fun i j => Disjoint (bands i) (bands j)) →
      (∀ j,0 < bandReciprocalMass (bands j)) →
      ∀ (Y θ H u v U : ℝ) (l r : ℕ) (β : ℕ → ℂ),
      0 < Y → 0 < H → 0 < U → 1 ≤ H*U → H*U ≤ Real.exp (σ*L) →
      H ≤ u → v ≤ 2*H → 1 ≤ Real.log u → U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
      (∀ n ∈ Icc l r,‖β n‖ ≤ L^D) →
      ∀ (k q : ℕ) (χb : DirichletCharacter ℂ k) (χ : DirichletCharacter ℂ q) (modulation c scale : ℝ), 1 ≤ scale →
      ∀ (n : ℕ) (R : ℝ), 0 ≤ R →
      (∫ t : ℝ in {t | R ≤ |t-c|},markedMajorFourierWeight (scale*(H*U)) (n+2) (t-c)*
        ‖markedMajorLabelEndpoint bands cutoff χb θ Y χ (Real.exp (L^(6/25:ℝ))) modulation H u v U l r β t‖^2) ≤
          ((1+R/(scale*(H*U)))^n)⁻¹*(C*scale*L^(2*D+5)) := by
  obtain ⟨C,hC,hmean⟩ := marked_major_label_translated_mean σ D B hσ hB cutoff hcutoff hsupp
  refine ⟨markedMajorLocalMeanConstant*(3*C/2),mul_pos markedMajorLocalMeanConstant_pos (by positivity),?_⟩
  filter_upwards [hmean,eventually_ge_atTop (1:ℝ)] with L hL hLone
  intro J _ bands hbands hdis hV Y θ H u v U l r β hY hH hU hX hXupper hHu hv hlog hl hr hβ
    k q χb χ modulation c scale hscale
  let W : ℝ := Real.exp (L^(6/25:ℝ))
  let Q := markedMajorLabelEndpoint bands cutoff χb θ Y χ W modulation H u v U l r β
  have hQc : Continuous Q := markedMajorLabelEndpoint_continuous bands cutoff χb θ Y χ W modulation H u v U l r β
  obtain ⟨K,hK⟩ := markedMajorLabelEndpoint_bounded bands cutoff χb θ Y χ W modulation H u v U l r β
  have hscale0 : 0 < scale := zero_lt_one.trans_le hscale
  have hlocal (z : ℝ) :
      (∫ t in Set.Icc z (z+scale*(H*U)), ‖Q t‖^2) ≤ (3*C/2)*scale*L^(2*D+5) := by
    rw [markedMajor_local_integral_eq_translated _ z (scale*(H*U)) (by positivity)]
    have h := hL bands hbands hdis hV Y θ H u v U (scale*(H*U)/2)
      (z+scale*(H*U)/2) l r β hY hH hU (by positivity) hX hXupper hHu hv hlog hl hr hβ
      k q χb χ modulation
    have he : 1+(scale*(H*U)/2)/(H*U) = 1+scale/2 := by field_simp
    rw [he] at h
    apply h.trans
    have hLp : 0 ≤ C*L^(2*D+5) := by positivity
    calc
      _ ≤ C*L^(2*D+5)*(3*scale/2) := mul_le_mul_of_nonneg_left (by linarith) hLp
      _ = _ := by ring
  have hM : 0 ≤ (3*C/2)*scale*L^(2*D+5) := by positivity
  intro n R hR
  have h := markedMajorLocalMean_weighted_tail Q hQc K hK (mul_pos hscale0 (mul_pos hH hU)) hM hR hlocal c n
  simpa only [Q,W,mul_assoc] using h

end ArtinMatthews
