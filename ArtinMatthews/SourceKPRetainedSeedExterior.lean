module

public import ArtinMatthews.SourceKPResidualExteriorProduct
public import ArtinMatthews.SourceKPResidualUnitInitial
public import ArtinMatthews.SourceKPRetainedSeedSupport
public import ArtinMatthews.SourceKPResidualUnitNormalization
public import ArtinMatthews.SourceKPRetainedExteriorProduct
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

/-! The literal common-level seed coefficient at arbitrary finite
arguments, with exact exterior and rational frequency transport. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix StandardAdelic QuadraticWeil
open scoped NumberField MatrixGroups AdeleRing Classical BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "A" => GL (Fin 2) 𝔸ᶠ[K]
local notation "B" => sourceKPRetainedFiniteBase K hζ
local notation "D" => sourceKPFiniteAdeleProjectiveDiagonalLift K hζ
local notation "tuple" => sourceKPAdelicRootSupportTuple K hζ

def sourceKPRetainedSeedFourierAt (S : Finset Pr) (R M : S → ℕ)
    {T : ℝ} (hT : 1 ≤ T) (m : Kˣ) (q₀ qf : Gf) : ℂ :=
  ∑ i : SourceKPRetainedSeedIndex K S R M, sourceKPRetainedSeedWeight K S R M i *
    sourceKPCuspResidualFourierValue K hζ m hT (qf * sourceKPRetainedSeedTranslate K hζ S R M q₀ i)

theorem sourceKPRetainedSeedFourierAt_diagonal (S : Finset Pr) (R M : S → ℕ)
    {T : ℝ} (hT : 1 ≤ T) (q₀ : Gf) (z : ∀ P : S, (P.val.adicCompletion K)ˣ) :
    sourceKPRetainedSeedFourierAt K hζ S R M hT 1 q₀ (D (sourceKPRetainedDiagonalUnit K S z)) =
      sourceKPRetainedSeedCoefficient K hζ S R M hT q₀ z := rfl

theorem sourceKPRetainedSeedFourierAt_unit_translate (S : Finset Pr) (R M : S → ℕ)
    {T : ℝ} (hT : 1 ≤ T) (m : Kˣ) (q₀ qf : Gf) :
    sourceKPRetainedSeedFourierAt K hζ S R M hT 1 q₀
        (sourceKPCuspResidualUnitTranslate K hζ m qf) =
      sourceKPCuspResidualFrequencyScale K hζ m (1/6) *
        sourceKPRetainedSeedFourierAt K hζ S R M hT m q₀ qf := by
  unfold sourceKPRetainedSeedFourierAt
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : sourceKPCuspResidualUnitTranslate K hζ m qf *
      sourceKPRetainedSeedTranslate K hζ S R M q₀ i =
      sourceKPCuspResidualUnitTranslate K hζ m (qf * sourceKPRetainedSeedTranslate K hζ S R M q₀ i) :=
    mul_assoc _ _ _
  rw [he, sourceKPCuspResidualFourierValue_unit_translate]
  ring

local notation "S[" S₀ "]" => sourceHilbertSet K S₀

theorem sourceKPRetainedSeedFourierAt_exterior
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ S[S₀])
    (R M : S[S₀] → ℕ) {T : ℝ} (hT : 2 < T)
    (q₀ : Gf) (hq₀ : ∀ P ∉ S[S₀], B P q₀ = 1) (z : ∀ P : S[S₀], (P.val.adicCompletion K)ˣ)
    (a : A) (U : Finset Pr) (hUS : Disjoint U S[S₀]) :
    sourceKPRetainedSeedFourierAt K hζ S[S₀] R M (one_le_two.trans hT.le) 1 q₀
        (D (sourceKPRetainedDiagonalUnit K S[S₀] z) * (tuple 1 a U).2) =
      sourceKPRetainedSeedCoefficient K hζ S[S₀] R M (one_le_two.trans hT.le) q₀ z *
        ∏ P ∈ U, sourceKPResidualExteriorFactor K hζ S₀ hS a P := by
  let S := S[S₀]
  let v := D (sourceKPRetainedDiagonalUnit K S z)
  let W := sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le)
  let E := (tuple 1 a U).2
  let L := ∏ P ∈ U, sourceKPResidualExteriorFactor K hζ S₀ hS a P
  let t := sourceKPRetainedSeedTranslate K hζ S[S₀] R M q₀
  have hPS (P : Pr) (hP : P ∈ U) : P ∉ S[S₀] := (Finset.disjoint_left.mp hUS) hP
  have ht (P : Pr) (hP : P ∈ U) (i : SourceKPRetainedSeedIndex K S[S₀] R M) :
      B P (t i) = 1 :=
    sourceKPRetainedFiniteBase_seedTranslate_notMem K hζ S[S₀] R M q₀ i P (hPS P hP) (hq₀ P (hPS P hP))
  have he (i : SourceKPRetainedSeedIndex K S[S₀] R M) : W ((v*E)*t i) = W (v*t i)*L := by
    have hc := sourceKPRetainedExteriorTuple_commute K hζ a U (t i) (fun P hP => ht P hP i)
    have hb : ∀ P ∈ U, B P (v*t i) = 1 := by
      intro P hP
      rw [map_mul, sourceKPRetainedFiniteBase_diagonalUnit_notMem K hζ S[S₀] z P (hPS P hP),
        ht P hP i, one_mul]
    rw [mul_assoc, hc.eq, ← mul_assoc]
    exact sourceKPResidualFourierValue_exterior_product_of_supported K hζ S₀ hS hT a U hUS (v*t i) hb
  change (∑ i, sourceKPRetainedSeedWeight K S[S₀] R M i * W ((v*E)*t i)) =
    (∑ i, sourceKPRetainedSeedWeight K S[S₀] R M i * W (v*t i))*L
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [he, mul_assoc]

end
end ArtinMatthews
