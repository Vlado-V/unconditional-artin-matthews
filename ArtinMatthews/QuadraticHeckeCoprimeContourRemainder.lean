module

public import ArtinMatthews.QuadraticHeckeMainTermEuler
public import ArtinMatthews.VaryingKummerAnalyticMixedZetaZero
public import OAI.NumberTheory.DirichletL.Detector.Physical
public import ArtinMatthews.QuadraticHeckeCoprimeDensity
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
public import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.Topology.Sheaves.Init
import ArtinMatthews.SourceContourHeightWeight


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Complex Set MeasureTheory VaryingKummerAnalytic SourcePhysical
  UniqueFactorizationMonoid
open OAI.SevenEighths.ProbePhysical
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]

/-- The finite Möbius sum of the contour integrals at their actual divisor scales. -/
def quadraticHeckeCoprimeContourRemainder (m : Ideal (𝓞 F))
    (H : ℂ → ℂ) (σ X : ℝ) : ℂ :=
  ∑ d ∈ HeckeIdealMobius.divisors F m, (moebius d : ℂ) *
    verticalIntegral σ (fun s : ℂ =>
      (((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) ^ s) * H s * mixedDedekindZeta F s)

theorem quadraticHeckeCoprime_divisor_norm_pos
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) {d : Ideal (𝓞 F)}
    (hd : d ∈ HeckeIdealMobius.divisors F m) : 0 < (Ideal.absNorm d : ℝ) := by
  have hd0 : d ≠ ⊥ := by
    intro hzero
    obtain ⟨J, hJ⟩ := (HeckeIdealMobius.mem_divisors F hm).mp hd
    exact hm (by rw [hJ, hzero, Ideal.bot_mul])
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hd0)

/-- The residue factors out of the finite Möbius sum without changing the contour terms. -/
theorem quadraticHeckeCoprimeContour_residue
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (H : ℂ → ℂ) (σ X : ℝ) (A B : ℂ) :
    (∑ d ∈ HeckeIdealMobius.divisors F m, (moebius d : ℂ) *
      (verticalIntegral σ (fun s : ℂ =>
        (((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) ^ s) * H s * mixedDedekindZeta F s) +
          A * ((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) * B)) =
      quadraticHeckeCoprimeContourRemainder F m H σ X +
        A * (X : ℂ) * B * quadraticHeckeCoprimeDensity F m := by
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  change quadraticHeckeCoprimeContourRemainder F m H σ X + _ = _
  congr 1
  calc
    _ = ∑ d ∈ HeckeIdealMobius.divisors F m,
        (moebius d : ℂ) * ((A * B) * ((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ)) := by
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = (A * B) * (X : ℂ) * quadraticHeckeCoprimeDensity F m :=
      quadraticHeckeCoprimeDensity_rescaled_sum F m hm X (A * B)
    _ = _ := by ring

end
end ArtinMatthews
