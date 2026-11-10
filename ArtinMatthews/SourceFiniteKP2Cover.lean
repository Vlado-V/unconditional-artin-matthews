module

public import ArtinMatthews.SourceFiniteKPMultipliers
public import ArtinMatthews.SourceKubotaCocycle
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

/-! The actual local threefold GL2 group law built from the normalized
cubic reciprocity multiplier. The projection and central kernel are
constructed on this group. Compact and adelic splittings are separate. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section

structure SourceFiniteKP2Cover (K : Type) [Field K] [NumberField K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 12) (P : HeightOneSpectrum (𝓞 K)) where
  central : rootsOfUnity 3 (P.adicCompletion K)
  base : GL (Fin 2) (P.adicCompletion K)

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

@[ext] theorem SourceFiniteKP2Cover.ext {x y : SourceFiniteKP2Cover K hζ P}
    (hc : x.central = y.central) (hb : x.base = y.base) : x = y := by
  cases x
  cases y
  congr

instance sourceFiniteKP2CoverGroup : Group (SourceFiniteKP2Cover K hζ P) where
  mul x y := ⟨x.central * y.central * sourceFiniteKP2Multiplier K hζ P x.base y.base, x.base * y.base⟩
  one := ⟨1, 1⟩
  inv x := ⟨(x.central * sourceFiniteKP2Multiplier K hζ P x.base⁻¹ x.base)⁻¹, x.base⁻¹⟩
  mul_assoc x y z := by
    apply SourceFiniteKP2Cover.ext
    · change (x.central * y.central * sourceFiniteKP2Multiplier K hζ P x.base y.base) * z.central *
          sourceFiniteKP2Multiplier K hζ P (x.base * y.base) z.base =
        x.central * (y.central * z.central * sourceFiniteKP2Multiplier K hζ P y.base z.base) *
          sourceFiniteKP2Multiplier K hζ P x.base (y.base * z.base)
      calc
        _ = (x.central * y.central * z.central) *
            (sourceFiniteKP2Multiplier K hζ P x.base y.base *
              sourceFiniteKP2Multiplier K hζ P (x.base * y.base) z.base) := by ac_rfl
        _ = _ := by rw [sourceFiniteKP2Multiplier_cocycle]; ac_rfl
    · exact mul_assoc x.base y.base z.base
  one_mul x := by
    apply SourceFiniteKP2Cover.ext
    · change 1 * x.central * sourceFiniteKP2Multiplier K hζ P 1 x.base = x.central
      rw [one_mul, sourceFiniteKP2Multiplier_one_left, mul_one]
    · exact one_mul x.base
  mul_one x := by
    apply SourceFiniteKP2Cover.ext
    · change x.central * 1 * sourceFiniteKP2Multiplier K hζ P x.base 1 = x.central
      rw [mul_one, sourceFiniteKP2Multiplier_one_right, mul_one]
    · exact mul_one x.base
  inv_mul_cancel x := by
    apply SourceFiniteKP2Cover.ext
    · change (x.central * sourceFiniteKP2Multiplier K hζ P x.base⁻¹ x.base)⁻¹ * x.central *
          sourceFiniteKP2Multiplier K hζ P x.base⁻¹ x.base = 1
      rw [mul_assoc, inv_mul_cancel]
    · exact inv_mul_cancel x.base

def sourceFiniteKP2Projection : SourceFiniteKP2Cover K hζ P →* GL (Fin 2) (P.adicCompletion K) where
  toFun := SourceFiniteKP2Cover.base
  map_one' := rfl
  map_mul' _ _ := rfl

def sourceFiniteKP2Center : rootsOfUnity 3 (P.adicCompletion K) →* SourceFiniteKP2Cover K hζ P where
  toFun z := ⟨z, 1⟩
  map_one' := rfl
  map_mul' z w := by
    apply SourceFiniteKP2Cover.ext
    · change z * w = z * w * sourceFiniteKP2Multiplier K hζ P 1 1
      rw [sourceFiniteKP2Multiplier_one_left, mul_one]
    · exact (one_mul _).symm

theorem sourceFiniteKP2Center_injective : Function.Injective (sourceFiniteKP2Center K hζ P) :=
  fun _ _ h => congrArg SourceFiniteKP2Cover.central h

theorem sourceFiniteKP2Projection_surjective : Function.Surjective (sourceFiniteKP2Projection K hζ P) :=
  fun g => ⟨⟨1, g⟩, rfl⟩

theorem sourceFiniteKP2Cover_exact :
    (sourceFiniteKP2Center K hζ P).range = (sourceFiniteKP2Projection K hζ P).ker := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    rfl
  · intro hx
    change x.base = 1 at hx
    exact ⟨x.central, SourceFiniteKP2Cover.ext K hζ P rfl hx.symm⟩

theorem sourceFiniteKP2Center_commute (z : rootsOfUnity 3 (P.adicCompletion K))
    (x : SourceFiniteKP2Cover K hζ P) : Commute (sourceFiniteKP2Center K hζ P z) x := by
  apply SourceFiniteKP2Cover.ext
  · change z * x.central * sourceFiniteKP2Multiplier K hζ P 1 x.base =
      x.central * z * sourceFiniteKP2Multiplier K hζ P x.base 1
    rw [sourceFiniteKP2Multiplier_one_left, sourceFiniteKP2Multiplier_one_right, mul_one, mul_one, mul_comm]
  · change 1 * x.base = x.base * 1
    rw [one_mul, mul_one]

def sourceFiniteKP2Lift (g : GL (Fin 2) (P.adicCompletion K)) : SourceFiniteKP2Cover K hζ P :=
  ⟨1, g⟩

theorem sourceFiniteKP2Lift_mul (g h : GL (Fin 2) (P.adicCompletion K)) :
    sourceFiniteKP2Lift K hζ P g * sourceFiniteKP2Lift K hζ P h =
      sourceFiniteKP2Center K hζ P (sourceFiniteKP2Multiplier K hζ P g h) *
        sourceFiniteKP2Lift K hζ P (g * h) := by
  apply SourceFiniteKP2Cover.ext
  · change 1 * 1 * sourceFiniteKP2Multiplier K hζ P g h =
      sourceFiniteKP2Multiplier K hζ P g h * 1 * sourceFiniteKP2Multiplier K hζ P 1 (g * h)
    rw [one_mul, one_mul, mul_one, sourceFiniteKP2Multiplier_one_left, mul_one]
  · change g * h = 1 * (g * h)
    rw [one_mul]

end
end ArtinMatthews
