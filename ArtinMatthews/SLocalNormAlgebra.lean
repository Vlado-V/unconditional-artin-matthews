module

public import ArtinMatthews.SLocalLogarithm
public import ArtinMatthews.AllowedGeneratorSelection
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! The actual product-formula S-norm descends through the genuine
principal-ideal kernel to a positive multiplicative norm on fractional
ideals of the constructed S-integer PID. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain SUnitGroup FractionalIdeal
open scoped NumberField Classical BigOperators
noncomputable section
variable (K : Type) [Field K] [NumberField K]

@[simp] theorem sLocalNorm_one (S : Finset (HeightOneSpectrum (𝓞 K))) :
    sLocalNorm K S 1 = 1 := by
  change Real.exp (sLocalLogSum K S 0) = 1
  rw [map_zero, Real.exp_zero]

@[simp] theorem sLocalNorm_inv (S : Finset (HeightOneSpectrum (𝓞 K))) (y : SWholeUnits K S) :
    sLocalNorm K S y⁻¹ = (sLocalNorm K S y)⁻¹ := by
  change Real.exp (sLocalLogSum K S (-Additive.ofMul y)) = _
  rw [map_neg, Real.exp_neg]
  rfl

@[simp] theorem sLocalNorm_div (S : Finset (HeightOneSpectrum (𝓞 K))) (x y : SWholeUnits K S) :
    sLocalNorm K S (x / y) = sLocalNorm K S x / sLocalNorm K S y := by
  rw [div_eq_mul_inv, sLocalNorm_mul, sLocalNorm_inv, div_eq_mul_inv]

def fieldSNorm (S : Finset (HeightOneSpectrum (𝓞 K))) : Kˣ →* ℝ where
  toFun a := sLocalNorm K S (sWholeDiagonal K S a)
  map_one' := by rw [map_one, sLocalNorm_one]
  map_mul' a b := by rw [map_mul, sLocalNorm_mul]

theorem fieldSNorm_pos (S : Finset (HeightOneSpectrum (𝓞 K))) (a : Kˣ) :
    0 < fieldSNorm K S a := sLocalNorm_pos K S _

@[simp] theorem fieldSNorm_sUnit (S : Finset (HeightOneSpectrum (𝓞 K)))
    (u : SUnitGroup (K := K) S) : fieldSNorm K S (u : Kˣ) = 1 := sLocalNorm_sUnit K S u

theorem fieldSNorm_eq_of_principal_eq (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (a b : Kˣ)
    (hI : toPrincipalIdeal (AllowedGenerators.sourceRing K S₀) K a =
      toPrincipalIdeal (AllowedGenerators.sourceRing K S₀) K b) :
    fieldSNorm K (sourceHilbertSet K S₀) a = fieldSNorm K (sourceHilbertSet K S₀) b := by
  let u : SUnitGroup (K := K) (sourceHilbertSet K S₀) :=
    ⟨a / b, (AllowedGenerators.principal_eq_iff_ratio_sUnit K S₀ a b).mp hI⟩
  calc
    _ = fieldSNorm K (sourceHilbertSet K S₀) ((u : Kˣ) * b) := by
      congr 1
      exact (div_mul_cancel a b).symm
    _ = fieldSNorm K (sourceHilbertSet K S₀) b := by rw [map_mul, fieldSNorm_sUnit, one_mul]

namespace AllowedGenerators

def idealSNorm {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) : idealGroup K S₀ →* ℝ where
  toFun I := fieldSNorm K (sourceHilbertSet K S₀) (generator K hζ S₀ I)
  map_one' := by
    calc
      _ = fieldSNorm K (sourceHilbertSet K S₀) 1 :=
        fieldSNorm_eq_of_principal_eq K S₀ _ _ (by rw [generator_principal, map_one])
      _ = 1 := map_one _
  map_mul' I J := by
    calc
      _ = fieldSNorm K (sourceHilbertSet K S₀)
          (generator K hζ S₀ I * generator K hζ S₀ J) :=
        fieldSNorm_eq_of_principal_eq K S₀ _ _ (by
          rw [generator_principal, map_mul, generator_principal, generator_principal])
      _ = _ := map_mul _ _ _

theorem idealSNorm_pos {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : idealGroup K S₀) :
    0 < idealSNorm K hζ S₀ I := fieldSNorm_pos K _ _

theorem idealSNorm_eq_of_generator {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : idealGroup K S₀) (a : Kˣ)
    (ha : toPrincipalIdeal (sourceRing K S₀) K a = I) :
    idealSNorm K hζ S₀ I = fieldSNorm K (sourceHilbertSet K S₀) a :=
  fieldSNorm_eq_of_principal_eq K S₀ _ _ ((generator_principal K hζ S₀ I).trans ha.symm)

end AllowedGenerators
end
end ArtinMatthews
