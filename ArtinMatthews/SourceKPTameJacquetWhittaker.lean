module

public import ArtinMatthews.SourceKPTameJacquetStableDomain
public import ArtinMatthews.SourceJacquetAdditiveTranslation
public import ArtinMatthews.SourceKPProjectiveCanonicalFactors
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual upper-root equivariance of stable Jacquet integration.
The positive character appears from translating the negative
integration phase on a ball containing the translation parameter. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical Filter
open scoped NumberField SourcePhysical MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "I₀" => sourceKPTameExteriorInducedSpace K hζ S₀ P
local notation "ρ₀" => sourceKPTameExteriorInducedRepresentation K hζ S₀ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "ψ₀" => localFiniteCharacter K P.val
local notation "B" => sourceLocalBall K P.val

theorem sourceKPTameJacquetInducedIntegrand_upper (f : I₀) (t x : L) :
    sourceKPTameJacquetInducedIntegrand K hζ S₀ P (ρ₀ (l₀ (sourceGL2Upper t)) f) x =
      ψ₀ t • sourceKPTameJacquetInducedIntegrand K hζ S₀ P f (x + t) := by
  change ψ₀ (-x) • f.val ((l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)) * l₀ (sourceGL2Upper t)) =
    ψ₀ t • (ψ₀ (-(x + t)) • f.val (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper (x + t))))
  rw [mul_assoc, sourceFiniteKP2ProjectiveLift_upper_add, smul_smul, ← AddChar.map_add_eq_mul,
    show t + -(x + t) = -x by abel]

theorem sourceKPTameJacquetInducedTruncation_upper (f : I₀) (t : L) (N : ℕ) (ht : t ∈ B (N : ℤ)) :
    sourceKPTameJacquetInducedTruncation K hζ S₀ P (ρ₀ (l₀ (sourceGL2Upper t)) f) N =
      ψ₀ t • sourceKPTameJacquetInducedTruncation K hζ S₀ P f N := by
  have hf := funext (sourceKPTameJacquetInducedIntegrand_upper K hζ S₀ P f t)
  unfold sourceKPTameJacquetInducedTruncation
  rw [hf, integral_smul, sourceJacquetBall_translate_integral K P.val (N : ℤ) t ht]

theorem sourceKPTameJacquetHasStableValue_upper {f : I₀} {j : ZMod 3 → ℂ}
    (hf : sourceKPTameJacquetHasStableValue K hζ S₀ P f j) (t : L) :
    sourceKPTameJacquetHasStableValue K hζ S₀ P (ρ₀ (l₀ (sourceGL2Upper t)) f) (ψ₀ t • j) := by
  filter_upwards [hf, sourceJacquetBall_eventually_contains K P.val t] with N hN ht
  refine ⟨?_, ?_⟩
  · rw [funext (sourceKPTameJacquetInducedIntegrand_upper K hζ S₀ P f t)]
    exact ((sourceJacquetBall_translate_integrable_iff K P.val (N : ℤ) t ht _).mpr hN.1).smul (ψ₀ t)
  · rw [sourceKPTameJacquetInducedTruncation_upper K hζ S₀ P f t N ht, hN.2]

end
end ArtinMatthews
