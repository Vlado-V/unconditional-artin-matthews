module

public import ArtinMatthews.SourceKPAdelicOutgoingLocalReceiver
public import ArtinMatthews.SourceKPCuspResidualFourierValue
public import ArtinMatthews.SourceKPAdelicOutgoingLocalRelation
public import ArtinMatthews.SourceKPResidualOutgoingKernel
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

/-! Actual local translate relations annihilate the corresponding
residual Fourier values at each finite remainder. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (hs : 0 < (1 / 6 : ℂ).re)

local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "B₀" => SourceFiniteKPProjectiveBorel K hζ P
local notation "s₀" => (1 / 6 : ℂ)
local notation "ρ₀" => sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation K hζ P s₀ hs
local notation "π₀" => sourceAlgebraicInducedRepresentation B₀ ρ₀
local notation "R₀" => sourceKPAdelicOutgoingRegularizedLocalSection K hζ P s₀ hs
local notation "ι₀" => sourceKPAdelicLocalProjective K hζ P
local notation "τ" => fun g : G => Prod.snd (ι₀ g)

theorem sourceKPCuspResidualFourierValue_sum_eq_zero_of_local_outgoing_relation
    {I : Type} [Fintype I] (g : I → G) (a : I → ℂ)
    (hrel : (∑ i, a i • π₀ (g i) (R₀).val) = 0)
    {T : ℝ} (hT : 2 < T) (qf : Gf) :
    (∑ i : I, a i * sourceKPCuspResidualFourierValue K hζ 1
      (one_le_two.trans hT.le) (qf * τ (g i))) = 0 := by
  have hout : SourceKPResidualOutgoingRelation K hζ (fun i => τ (g i)) a := by
    rw [sourceKPResidualOutgoingRelation_iff]
    change (∑ i, a i • sourceKPAdelicPrincipalSeriesRepresentation K hζ (-s₀)
      (ι₀ (g i)) (sourceKPAdelicOutgoingRegularizedSection K hζ s₀ hs)) = 0
    exact (sourceKPAdelicOutgoingLocalTranslate_relation_iff K hζ P s₀ hs Finset.univ g a).mp hrel
  exact sourceKPCuspResidualFourierValue_sum_eq_zero_of_outgoing_relation K hζ
    (fun i => τ (g i)) a hout hT 1 qf

end
end ArtinMatthews
