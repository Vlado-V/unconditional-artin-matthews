module

public import ArtinMatthews.SourceKPLocalUniformizerAction
public import ArtinMatthews.SourceKPTameParametric
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

/-! A three-coordinate receiver into the actual global torus carrier.
The cycle is derived from the global cubic character. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (π : (P.adicCompletion K)ˣ)

def sourceKPLocalReceiverBasis (s : ℂ) (v : SourceKPAdelicTorusInducedSpace K hζ s) (i : ZMod 3) :
    SourceKPAdelicTorusInducedSpace K hζ s :=
  (sourceKPCubicPower (sourceKPLocalUniformizerCycle K hζ P π s) i).val v

def sourceKPLocalReceiver (s : ℂ) (v : SourceKPAdelicTorusInducedSpace K hζ s) :
    (ZMod 3 → ℂ) →ₗ[ℂ] SourceKPAdelicTorusInducedSpace K hζ s :=
  (Pi.basisFun ℂ (ZMod 3)).constr ℂ (sourceKPLocalReceiverBasis K hζ P π s v)

theorem sourceKPLocalReceiver_basis (s : ℂ) (v : SourceKPAdelicTorusInducedSpace K hζ s) (i : ZMod 3) :
    sourceKPLocalReceiver K hζ P π s v (sourceJacquetBasis i) =
      sourceKPLocalReceiverBasis K hζ P π s v i := by
  have hi : sourceJacquetBasis i = (Pi.basisFun ℂ (ZMod 3)) i :=
    (Pi.basisFun_apply ℂ (ZMod 3) i).symm
  unfold sourceKPLocalReceiver
  rw [hi]
  exact (Pi.basisFun ℂ (ZMod 3)).constr_basis ℂ (sourceKPLocalReceiverBasis K hζ P π s v) i

theorem sourceKPLocalReceiver_zero (s : ℂ) (v : SourceKPAdelicTorusInducedSpace K hζ s) :
    sourceKPLocalReceiver K hζ P π s v (sourceJacquetBasis 0) = v := by
  rw [sourceKPLocalReceiver_basis, sourceKPLocalReceiverBasis, sourceKPCubicPower_zero]
  rfl

theorem sourceKPLocalReceiverBasis_shift
    (hπ : sourceKPFiniteVal K P (π : P.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (s : ℂ) (v : SourceKPAdelicTorusInducedSpace K hζ s) (i : ZMod 3) :
    (sourceKPLocalUniformizerCycle K hζ P π s).val (sourceKPLocalReceiverBasis K hζ P π s v i) =
      sourceKPLocalReceiverBasis K hζ P π s v (i+1) := by
  let A := sourceKPLocalUniformizerCycle K hζ P π s
  have hA : A^3 = 1 := sourceKPLocalUniformizerCycle_cube K hζ P π hπ s
  have hone : sourceKPCubicPower A (1 : ZMod 3) = A := by
    simp only [sourceKPCubicPower, ZMod.val_one, pow_one]
  have hm : A * sourceKPCubicPower A i = sourceKPCubicPower A (i+1) := by
    calc
      A * sourceKPCubicPower A i = sourceKPCubicPower A 1 * sourceKPCubicPower A i :=
        congrArg (fun B => B * sourceKPCubicPower A i) hone.symm
      _ = sourceKPCubicPower A (1+i) := (sourceKPCubicPower_add A hA 1 i).symm
      _ = sourceKPCubicPower A (i+1) := congrArg (sourceKPCubicPower A) (add_comm _ _)
  change (A : Module.End ℂ (SourceKPAdelicTorusInducedSpace K hζ s))
      ((sourceKPCubicPower A i).val v) = (sourceKPCubicPower A (i+1)).val v
  rw [← Module.End.mul_apply, ← Units.val_mul, hm]

theorem sourceKPLocalReceiver_uniformizer
    (h6 : (6 : 𝓞 K) ∉ P.asIdeal)
    (hπ : sourceKPFiniteVal K P (π : P.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (s : ℂ) (v : SourceKPAdelicTorusInducedSpace K hζ s) :
    (sourceKPLocalReceiver K hζ P π s v).comp
        (sourceKPTameParametricBorelRepresentation K hζ P h6 π hπ s
          (sourceFiniteKPProjectiveBorelDiagonal K hζ P π)) =
      (sourceKPAdelicLocalBorelRepresentation K hζ P s
        (sourceFiniteKPProjectiveBorelDiagonal K hζ P π)).comp (sourceKPLocalReceiver K hζ P π s v) := by
  apply (Pi.basisFun ℂ (ZMod 3)).ext
  intro i
  simp only [LinearMap.comp_apply, Pi.basisFun_apply]
  change sourceKPLocalReceiver K hζ P π s v
      (sourceKPTameParametricBorelRepresentation K hζ P h6 π hπ s
        (sourceFiniteKPProjectiveBorelDiagonal K hζ P π) (sourceJacquetBasis i)) =
    sourceKPAdelicLocalBorelRepresentation K hζ P s
      (sourceFiniteKPProjectiveBorelDiagonal K hζ P π)
      (sourceKPLocalReceiver K hζ P π s v (sourceJacquetBasis i))
  have hl := sourceKPTameParametricBorel_uniformizer_basis K hζ P h6 π hπ s (1 : ℤ) i
  simp only [zpow_one, Int.cast_one, mul_one] at hl
  rw [hl, map_smul, sourceKPLocalReceiver_basis, sourceKPLocalReceiver_basis,
    sourceKPLocalUniformizer_generator]
  exact congrArg
    (fun w => Complex.exp (-(s+1/2)*(Real.log (Ideal.absNorm P.asIdeal : ℝ) : ℂ)) • w)
    (sourceKPLocalReceiverBasis_shift K hζ P π hπ s v i).symm

end
end ArtinMatthews
