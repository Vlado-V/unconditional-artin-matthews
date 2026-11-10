module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import ArtinMatthews.MarkedMajorArcEnergyCover
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

/-! Exceptional intervals in a measurable high-time part of the window. -/

namespace ArtinMatthews

open Finset MeasureTheory Set

theorem sourceComparison_isolated_energy_subset (P M N : ℝ → ℂ) (I : Finset ℤ)
    (T ε p m E B : ℝ) (D : Set ℝ) (hD : MeasurableSet D)
    (hDT : D ⊆ Set.Icc (-T) T) (hP : Continuous P) (hM : Continuous M) (hN : Continuous N)
    (hPb : ∀ t ∈ D, ‖P t‖ ≤ p)
    (hMb : ∀ t ∈ D, ‖M t‖ ≤ m)
    (hcover : ∀ t ∈ D, ε < ‖P t‖ →
      ∃ z ∈ I, t ∈ Set.Icc (z:ℝ) ((z:ℝ)+1))
    (hmean : (∫ t in D, ‖M t*N t‖^2) ≤ E)
    (hsparse : (∑ z ∈ I, sSup ((fun t => ‖N t‖^2) ''
      Set.Icc (z:ℝ) ((z:ℝ)+1))) ≤ B) :
    (∫ t in D, ‖P t*M t*N t‖^2) ≤ ε^2*E+p^2*m^2*B := by
  have hmaj := markedUnitEnergyMajorant_integrable I hN
  have hpoint (t : ℝ) (ht : t ∈ D) :
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
  have hf : IntegrableOn (fun t => ‖P t*M t*N t‖^2) D :=
    (((hP.mul hM).mul hN).norm.pow 2).integrableOn_Icc.mono_set hDT
  have hg1 : IntegrableOn (fun t => ε^2*‖M t*N t‖^2) D :=
    (((hM.mul hN).norm.pow 2).integrableOn_Icc.mono_set hDT).const_mul (ε^2)
  have hg2 : IntegrableOn (fun t => p^2*m^2*markedUnitEnergyMajorant I N t) D :=
    hmaj.integrableOn.const_mul (p^2*m^2)
  have hg := hg1.add hg2
  calc
    _ ≤ ∫ t in D,
        ε^2*‖M t*N t‖^2+p^2*m^2*markedUnitEnergyMajorant I N t :=
      setIntegral_mono_on hf hg hD hpoint
    _ = ε^2*(∫ t in D, ‖M t*N t‖^2)+
        p^2*m^2*(∫ t in D, markedUnitEnergyMajorant I N t) := by
      rw [integral_add hg1 hg2,integral_const_mul,integral_const_mul]
    _ ≤ ε^2*E+p^2*m^2*B := add_le_add
      (mul_le_mul_of_nonneg_left hmean (sq_nonneg _))
      (mul_le_mul_of_nonneg_left
        ((setIntegral_le_integral hmaj (Filter.Eventually.of_forall
          (markedUnitEnergyMajorant_nonneg I N))).trans
          ((markedUnitEnergyMajorant_integral_le I hN).trans hsparse)) (by positivity))

end ArtinMatthews
