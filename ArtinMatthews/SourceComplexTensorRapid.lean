module

public import ArtinMatthews.SourceArchimedeanRapid
public import OAI.RepresentationTheory.Weil.AdelicSplitting.RealCharacters
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

namespace ArtinMatthews.VaryingKummerAnalytic
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped BigOperators SchwartzMap
noncomputable section
variable {ι : Type*} [Fintype ι]

def sourceComplexTensor (f : ι → 𝓢(ℂ, ℂ)) (x : ι → ℂ) : ℂ := ∏ i, f i (x i)

def sourceComplexTensorRapid (f : ι → 𝓢(ℂ, ℂ)) :
    RapidFunctions.LocalAnalysis.RapidFunction (ι → ℂ) :=
  RapidFunctions.LocalAnalysis.piRapidFunction
    (fun i => RapidFunctions.LocalAnalysis.schwartzRapidFunction (f i))

theorem sourceComplexTensorRapid_apply (f : ι → 𝓢(ℂ, ℂ)) (x : ι → ℂ) :
    sourceComplexTensorRapid f x = sourceComplexTensor f x := rfl

def sourceComplexTensorFourierRapid (f : ι → 𝓢(ℂ, ℂ)) :
    RapidFunctions.LocalAnalysis.RapidFunction (ι → ℂ) :=
  RapidFunctions.LocalAnalysis.piRapidFunction (fun i => sourceComplexTraceFourierRapid (f i))

theorem sourceComplexTensorFourierRapid_apply (f : ι → 𝓢(ℂ, ℂ)) (x : ι → ℂ) :
    sourceComplexTensorFourierRapid f x = sourceComplexProductFourier (sourceComplexTensor f) x := by
  change (∏ i, sourceComplexTraceFourier (f i) (x i)) = _
  exact (source_complex_product_fourier_tensor (fun i => f i) x).symm

theorem sourceRealCharacter_norm (t : ℝ) :
    ‖RealCharacters.LocalAnalysis.realCharacter 1 t‖ = 1 := by
  rw [RealCharacters.LocalAnalysis.realCharacter_apply, Complex.norm_exp]
  simp [Complex.mul_re]

end
end ArtinMatthews.VaryingKummerAnalytic
