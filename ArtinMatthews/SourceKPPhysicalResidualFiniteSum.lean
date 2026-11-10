module

public import ArtinMatthews.SourceKPPhysicalResidualSeries
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

/-! Actual finite translates and their source Bessel coefficients.
A common signed Weyl element rotates each translate in a branch. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain SourceReflection
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "V" => InfinitePlace K
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "L" => sourceKPAllInfinitePlaces K
local notation "D" => sourceSLocalProjectiveDiagonalLift K S hζ

variable {ι : Type} [Fintype ι]

def sourceKPPhysicalResidualFiniteValue
    (ε : V → Bool) {T : ℝ} (hT : 1 ≤ T) (g : ι → Gf) (a : ι → ℂ)
    (x : SWholeUnits K S) : ℂ :=
  ∑ i : ι, a i * sourceKPPhysicalResidualValue K hζ S ε hT (g i) x

theorem sourceKPPhysicalResidualFiniteValue_hasSum
    (ε : V → Bool) {T : ℝ} (hT : 1 ≤ T) (g : ι → Gf) (a : ι → ℂ)
    (x : SWholeUnits K S) :
    HasSum (fun m : Kˣ => ∑ i : ι, a i *
      sourceKPPhysicalResidualBesselTerm K hζ S ε hT ((D x).2 * g i) m x)
      (sourceKPPhysicalResidualFiniteValue K hζ S ε hT g a x) := by
  unfold sourceKPPhysicalResidualFiniteValue
  apply hasSum_sum
  intro i _
  exact (sourceKPPhysicalResidualValue_hasSum K hζ S ε hT (g i) x).mul_left (a i)

def sourceKPReflectedResidualFiniteValue (b : Kˣ)
    (ε : V → Bool) {T : ℝ} (hT : 1 ≤ T) (g : ι → Gf) (a : ι → ℂ)
    (x : SWholeUnits K S) : ℂ :=
  (sourceKPReflectionProductPhase K hζ b ε L)⁻¹ *
    sourceKPPhysicalResidualFiniteValue K hζ S ε hT g a
      (sourceKPSLocalReflectionArgument K S b * x⁻¹)

theorem sourceKPReflectedResidualFiniteValue_hasSum (b : Kˣ)
    (ε : V → Bool) {T : ℝ} (hT : 1 ≤ T) (g : ι → Gf) (a : ι → ℂ)
    (x : SWholeUnits K S) :
    HasSum (fun m : Kˣ => ∑ i : ι, a i *
      sourceKPPhysicalResidualBesselTerm K hζ S (fun v => !(ε v)) hT
        (sourceKPReflectedHorizontalFiber K hζ S b (g i) x) m x)
      (sourceKPReflectedResidualFiniteValue K hζ S b ε hT g a x) := by
  let y := sourceKPSLocalReflectionArgument K S b * x⁻¹
  let ω := sourceKPReflectionProductPhase K hζ b ε L
  change HasSum _ (ω⁻¹ * ∑ i : ι, a i * sourceKPPhysicalResidualValue K hζ S ε hT (g i) y)
  rw [Finset.mul_sum]
  apply hasSum_sum
  intro i _
  have h := sourceKPPhysicalResidualValue_reflection K hζ S b ε hT (g i) y
  change HasSum (fun m : Kˣ => sourceKPPhysicalResidualBesselTerm K hζ S (fun v => !(ε v)) hT
    (sourceKPReflectedHorizontalFiber K hζ S b (g i)
      (sourceKPSLocalReflectionArgument K S b*y⁻¹)) m
      (sourceKPSLocalReflectionArgument K S b*y⁻¹)) (ω⁻¹ * _ ) at h
  rw [show sourceKPSLocalReflectionArgument K S b*y⁻¹ = x from
    sourceKPSLocalReflectionArgument_involution K S b x] at h
  rw [mul_left_comm ω⁻¹]
  exact h.mul_left (a i)

theorem sourceKPPhysicalResidualFiniteValue_split
    {κ : Type} [Fintype κ] (partition : ι → κ) (ε : V → Bool) {T : ℝ} (hT : 1 ≤ T)
    (g : ι → Gf) (a : ι → ℂ) (x : SWholeUnits K S) :
    sourceKPPhysicalResidualFiniteValue K hζ S ε hT g a x =
      ∑ k : κ, ∑ i : ι, if partition i = k then
        a i * sourceKPPhysicalResidualValue K hζ S ε hT (g i) x else 0 := by
  rw [Finset.sum_comm]
  unfold sourceKPPhysicalResidualFiniteValue
  simp

end
end ArtinMatthews
