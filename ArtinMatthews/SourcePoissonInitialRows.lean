module

public import ArtinMatthews.SLocalNormAlgebra
public import ArtinMatthews.SourceGlobalEulerCoefficients
public import ArtinMatthews.SourcePoissonMellinHeight
public import ArtinMatthews.SourceGlobalEulerMajorant
public import ArtinMatthews.SourcePrimeNormSummability
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain MeasureTheory AllowedGenerators
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

/-- The positive source norm of an actual nonzero S-integer. -/
def sourcePoissonFrequencyNorm (u : {u : sourceRing F S₀ // u ≠ 0}) : ℝ :=
  fieldSNorm F (sourceHilbertSet F S₀)
    (Units.mk0 (u.val : F) (fun h => u.property (Subtype.ext h)))

theorem sourcePoissonFrequencyNorm_pos (u : {u : sourceRing F S₀ // u ≠ 0}) :
    0 < sourcePoissonFrequencyNorm F S₀ u :=
  fieldSNorm_pos F _ _

variable [IsTotallyComplex F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)

theorem sourceGlobalEulerTerm_initial_continuous (u : sourceRing F S₀)
    (a : SourceExponentCoordinates F S₀) :
    Continuous (fun p : SourcePoissonHeights =>
      sourceGlobalEulerTerm F hζ S₀ hS η u
        (sourcePoissonVertical 4 p.2) (sourcePoissonVertical 4 p.1.1)
        (sourcePoissonVertical 2 p.1.2) a) := by
  unfold sourceGlobalEulerTerm
  simp_rw [Complex.cpow_def_of_ne_zero
    (Nat.cast_ne_zero.mpr (sourcePrimeExponentNorm_pos F S₀ a.1.val).ne'),
    Complex.cpow_def_of_ne_zero
    (Nat.cast_ne_zero.mpr (sourcePrimeExponentNorm_pos F S₀ a.2.1).ne'),
    Complex.cpow_def_of_ne_zero
    (Nat.cast_ne_zero.mpr (sourcePrimeExponentNorm_pos F S₀ a.2.2.1).ne'),
    Complex.cpow_def_of_ne_zero
    (Nat.cast_ne_zero.mpr (sourcePrimeExponentNorm_pos F S₀ a.2.2.2).ne')]
  unfold sourcePoissonVertical
  fun_prop

theorem sourceGlobalCalF_initial_measurable (u : sourceRing F S₀) :
    Measurable (fun p : SourcePoissonHeights =>
      sourceGlobalCalF F hζ S₀ hS η u
        (sourcePoissonVertical 4 p.2) (sourcePoissonVertical 4 p.1.1)
        (sourcePoissonVertical 2 p.1.2)) := by
  let : Countable (Ideal (𝓞 F)) := by
    apply Set.countable_univ_iff.mp
    apply (Set.countable_iUnion (fun n : ℕ =>
      (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) n).countable)).mono
    intro I _
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨Ideal.absNorm I, le_rfl⟩
  let : Countable (HeightOneSpectrum (𝓞 F)) := HeightOneSpectrum.asIdeal_injective.countable
  unfold sourceGlobalCalF
  exact Measurable.tsum (fun a => (sourceGlobalEulerTerm_initial_continuous F S₀ hζ hS η u a).measurable)

/-- The exact finite sum over the nonzero source frequency representatives on lines (4,4,2). -/
def sourcePoissonInitialRows (U : Finset {u : sourceRing F S₀ // u ≠ 0})
    (p : SourcePoissonHeights) : ℂ :=
  ∑ u ∈ U, (sourcePoissonFrequencyNorm F S₀ u : ℂ) ^ (-sourcePoissonVertical 2 p.1.2) *
    sourceGlobalCalF F hζ S₀ hS η u.val
      (sourcePoissonVertical 4 p.2) (sourcePoissonVertical 4 p.1.1) (sourcePoissonVertical 2 p.1.2)

theorem sourcePoissonInitialRows_measurable (U : Finset {u : sourceRing F S₀ // u ≠ 0}) :
    Measurable (sourcePoissonInitialRows F S₀ hζ hS η U) := by
  unfold sourcePoissonInitialRows
  apply Finset.measurable_sum
  intro u hu
  have hc : Continuous (fun p : SourcePoissonHeights =>
      (sourcePoissonFrequencyNorm F S₀ u : ℂ) ^ (-sourcePoissonVertical 2 p.1.2)) := by
    simp_rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (sourcePoissonFrequencyNorm_pos F S₀ u).ne')]
    unfold sourcePoissonVertical
    fun_prop
  exact hc.measurable.mul (sourceGlobalCalF_initial_measurable F S₀ hζ hS η u.val)

def sourcePoissonInitialRowBound (U : Finset {u : sourceRing F S₀ // u ≠ 0}) : ℝ :=
  ∑ u ∈ U, (sourcePoissonFrequencyNorm F S₀ u) ^ (-(2 : ℝ)) *
    ∑' a : SourceExponentCoordinates F S₀, sourceCoordinateMajorant F S₀ 3 10 3 12 a

theorem sourcePoissonInitialRows_norm_le (U : Finset {u : sourceRing F S₀ // u ≠ 0})
    (p : SourcePoissonHeights) :
    ‖sourcePoissonInitialRows F S₀ hζ hS η U p‖ ≤ sourcePoissonInitialRowBound F S₀ U := by
  unfold sourcePoissonInitialRows sourcePoissonInitialRowBound
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro u hu
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (sourcePoissonFrequencyNorm_pos F S₀ u),
    Complex.neg_re, sourcePoissonVertical_re]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (sourcePoissonFrequencyNorm_pos F S₀ u).le _)
  have h := sourceGlobalCalF_norm_le F S₀ hζ hS η u.val (sourcePoissonVertical 4 p.2)
    (sourcePoissonVertical 4 p.1.1) (sourcePoissonVertical 2 p.1.2) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num only [sourcePoissonVertical_re] at h
  exact h

end
end ArtinMatthews.SourceEulerAssembly
