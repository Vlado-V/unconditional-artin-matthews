module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Actual integration over the exceptional unit intervals. The cover uses
closed intervals, matching the literal supremum energy in the sparse lemma. -/
namespace ArtinMatthews
open Finset MeasureTheory Set

noncomputable def markedUnitEnergyMajorant (I : Finset ℤ) (N : ℝ → ℂ) (t : ℝ) : ℝ :=
  ∑ z ∈ I, (Set.Icc (z:ℝ) ((z:ℝ)+1)).indicator (fun s => ‖N s‖^2) t

lemma markedUnitEnergyMajorant_nonneg (I : Finset ℤ) (N : ℝ → ℂ) (t : ℝ) :
    0 ≤ markedUnitEnergyMajorant I N t := by
  apply sum_nonneg
  intro z _
  exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) _

lemma markedUnitEnergyMajorant_integrable (I : Finset ℤ) {N : ℝ → ℂ}
    (hN : Continuous N) : Integrable (markedUnitEnergyMajorant I N) := by
  apply integrable_finsetSum
  intro z _
  exact (integrable_indicator_iff measurableSet_Icc).2 (hN.norm.pow 2).integrableOn_Icc

lemma markedUnitEnergyMajorant_dominates (I : Finset ℤ) (N : ℝ → ℂ) (t : ℝ)
    (hcover : ∃ z ∈ I, t ∈ Set.Icc (z:ℝ) ((z:ℝ)+1)) :
    ‖N t‖^2 ≤ markedUnitEnergyMajorant I N t := by
  obtain ⟨z,hz,ht⟩ := hcover
  have hh := single_le_sum (f := fun j : ℤ => (Set.Icc (j:ℝ) ((j:ℝ)+1)).indicator
    (fun s => ‖N s‖^2) t) (fun j _ =>
    Set.indicator_nonneg (fun s _ => sq_nonneg (‖N s‖)) t) hz
  simpa only [Set.indicator_of_mem ht,markedUnitEnergyMajorant] using hh

lemma markedUnitEnergyMajorant_integral_le (I : Finset ℤ) {N : ℝ → ℂ}
    (hN : Continuous N) :
    (∫ t, markedUnitEnergyMajorant I N t) ≤
      ∑ z ∈ I, sSup ((fun t => ‖N t‖^2) '' Set.Icc (z:ℝ) ((z:ℝ)+1)) := by
  unfold markedUnitEnergyMajorant
  rw [integral_finsetSum]
  · apply sum_le_sum
    intro z _
    rw [integral_indicator measurableSet_Icc]
    let B := sSup ((fun t => ‖N t‖^2) '' Set.Icc (z:ℝ) ((z:ℝ)+1))
    have hb : BddAbove ((fun t => ‖N t‖^2) '' Set.Icc (z:ℝ) ((z:ℝ)+1)) :=
      (isCompact_Icc.image (hN.norm.pow 2)).bddAbove
    have hh := setIntegral_mono_on (μ := volume) (hN.norm.pow 2).integrableOn_Icc
      (integrableOn_const (measure_Icc_lt_top.ne)) measurableSet_Icc
      (fun t ht => le_csSup hb (Set.mem_image_of_mem _ ht))
    calc
      _ ≤ ∫ _t in Set.Icc (z:ℝ) ((z:ℝ)+1), B := hh
      _ = B := by rw [setIntegral_const,Real.volume_real_Icc_of_le (by linarith)]; simp
  · intro z _
    exact (integrable_indicator_iff measurableSet_Icc).2 (hN.norm.pow 2).integrableOn_Icc

/-- Integrate the small-prime/large-prime split with the actual unit cover,
retaining the product mean square and literal exceptional suprema. -/
theorem marked_isolated_energy_cover (P M N : ℝ → ℂ) (I : Finset ℤ)
    (T ε p m E B : ℝ) (hP : Continuous P) (hM : Continuous M) (hN : Continuous N)
    (hPb : ∀ t ∈ Set.Icc (-T) T, ‖P t‖ ≤ p)
    (hMb : ∀ t ∈ Set.Icc (-T) T, ‖M t‖ ≤ m)
    (hcover : ∀ t ∈ Set.Icc (-T) T, ε < ‖P t‖ →
      ∃ z ∈ I, t ∈ Set.Icc (z:ℝ) ((z:ℝ)+1))
    (hmean : (∫ t in Set.Icc (-T) T, ‖M t*N t‖^2) ≤ E)
    (hsparse : (∑ z ∈ I, sSup ((fun t => ‖N t‖^2) ''
      Set.Icc (z:ℝ) ((z:ℝ)+1))) ≤ B) :
    (∫ t in Set.Icc (-T) T, ‖P t*M t*N t‖^2) ≤ ε^2*E+p^2*m^2*B := by
  have hmaj := markedUnitEnergyMajorant_integrable I hN
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (-T) T) :
      ‖P t*M t*N t‖^2 ≤ ε^2*‖M t*N t‖^2+p^2*m^2*markedUnitEnergyMajorant I N t := by
    have hmaj0 := markedUnitEnergyMajorant_nonneg I N t
    by_cases hsmall : ‖P t‖ ≤ ε
    · have hb : ‖P t*M t*N t‖^2 ≤ ε^2*‖M t*N t‖^2 := by
        rw [mul_assoc,norm_mul,mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hsmall 2) (sq_nonneg _)
      exact hb.trans (le_add_of_nonneg_right (by positivity))
    · have hb : ‖P t*M t*N t‖^2 ≤ p^2*m^2*markedUnitEnergyMajorant I N t := by
        simp only [norm_mul,mul_pow]
        apply mul_le_mul
        · exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hPb t ht) 2)
            (pow_le_pow_left₀ (norm_nonneg _) (hMb t ht) 2) (sq_nonneg _) (sq_nonneg _)
        · exact markedUnitEnergyMajorant_dominates I N t (hcover t ht (lt_of_not_ge hsmall))
        · positivity
        · positivity
      exact hb.trans (le_add_of_nonneg_left (by positivity))
  have hf : IntegrableOn (fun t => ‖P t*M t*N t‖^2) (Set.Icc (-T) T) :=
    (((hP.mul hM).mul hN).norm.pow 2).integrableOn_Icc
  have hg1 : IntegrableOn (fun t => ε^2*‖M t*N t‖^2) (Set.Icc (-T) T) :=
    ((hM.mul hN).norm.pow 2).integrableOn_Icc.const_mul (ε^2)
  have hg2 : IntegrableOn (fun t => p^2*m^2*markedUnitEnergyMajorant I N t) (Set.Icc (-T) T) :=
    hmaj.integrableOn.const_mul (p^2*m^2)
  have hg := hg1.add hg2
  calc
    _ ≤ ∫ t in Set.Icc (-T) T,
        ε^2*‖M t*N t‖^2+p^2*m^2*markedUnitEnergyMajorant I N t :=
      setIntegral_mono_on hf hg measurableSet_Icc hpoint
    _ = ε^2*(∫ t in Set.Icc (-T) T, ‖M t*N t‖^2)+
        p^2*m^2*(∫ t in Set.Icc (-T) T, markedUnitEnergyMajorant I N t) := by
      rw [integral_add hg1 hg2,integral_const_mul,integral_const_mul]
    _ ≤ ε^2*E+p^2*m^2*B := add_le_add
      (mul_le_mul_of_nonneg_left hmean (sq_nonneg _))
      (mul_le_mul_of_nonneg_left
        ((setIntegral_le_integral hmaj (Filter.Eventually.of_forall
          (markedUnitEnergyMajorant_nonneg I N))).trans
          ((markedUnitEnergyMajorant_integral_le I hN).trans hsparse)) (by positivity))

end ArtinMatthews
