module

public import ArtinMatthews.SourceKPAdelicOutgoingRetainedJacquetProfile
public import ArtinMatthews.SourceKPAdelicOutgoingRetainedResidualSlice
public import ArtinMatthews.SourceKPAdelicOutgoingRetainedDiagonalPhase
public import ArtinMatthews.SourceKPAdelicOutgoingRetainedResidualTensor
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The finite retained residue tensor at the product of two actual
diagonals is evaluated at their product coordinate. The genuine
cubic phase is outside the finite basis sum. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (places : Finset (HeightOneSpectrum (𝓞 K)))

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Gₛ" => SourceKPLocalCompactProductGroup K hζ places
local notation "A" => sourceKPAdelicOutgoingRetainedResidualCoefficient K hζ places
local notation "Ω" => sourceKPTameUniformizerCharacter K hζ

theorem sourceKPAdelicOutgoingRetainedDiagonalPhaseProduct_norm
    (m x : ∀ P : ↥places, (P.val.adicCompletion K)ˣ) :
    ‖∏ P : ↥places, ((Ω P.val (m P) (x P) : ℂˣ) : ℂ)‖ = 1 := by
  rw [norm_prod]
  simp only [sourceKPAdelicOutgoingRetainedDiagonalPhase_norm K hζ, Finset.prod_const_one]

variable (hs : 0 < (1 / 6 : ℂ).re)

local notation "Label" => SourceKPAdelicOutgoingRetainedJacquetLabel K hζ hs places
local notation "lift" => sourceKPAdelicOutgoingRetainedJacquetBasisLift K hζ
local notation "F" => sourceKPAdelicOutgoingRetainedJacquetBasisDiagonalProfile K hζ

theorem sourceKPAdelicOutgoingRetainedResidualCoefficient_diagonal_mul_tensor
    {T : ℝ} (hT : 2 < T) (qf : Gf)
    (hqf : ∀ P : ↥places, sourceKPAdelicLocalBase K hζ P.val (1,qf) = 1)
    (m x : ∀ P : ↥places, (P.val.adicCompletion K)ˣ) (a : Gₛ) :
    A hT qf (fun P => sourceFiniteKP2ProjectiveLift K hζ P.val (sourceGL2Diagonal (m P)) *
        sourceFiniteKP2ProjectiveLift K hζ P.val (sourceGL2Diagonal (x P)) * a P) =
      (∏ P : ↥places, ((Ω P.val (m P) (x P) : ℂˣ) : ℂ)) *
        ∑ k : Label, A hT qf (fun P => lift P.val hs (k P)) *
          ∏ P : ↥places, F P.val hs (k P) (a P) (m P * x P) := by
  have ht := sourceKPAdelicOutgoingRetainedResidualCoefficient_tensor K hζ places hs hT qf hqf
    (fun P => sourceFiniteKP2ProjectiveLift K hζ P.val (sourceGL2Diagonal (m P)) *
      sourceFiniteKP2ProjectiveLift K hζ P.val (sourceGL2Diagonal (x P)) * a P)
  refine ht.trans ?_
  simp_rw [sourceKPAdelicOutgoingRetainedJacquetBasisCoordinate_diagonal_mul K hζ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.prod_mul_distrib]
  ac_rfl

end
end ArtinMatthews
