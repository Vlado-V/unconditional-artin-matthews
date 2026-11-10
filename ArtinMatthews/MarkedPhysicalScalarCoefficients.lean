module

public import ArtinMatthews.MarkedPhysicalCoprimeScalarDetector
public import ArtinMatthews.MarkedPhysicalEndpointNormActual
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

/-! Restricting the input functions to the already-summed scalar
rectangles is exact, including for the literal fixed character factors. -/
namespace ArtinMatthews
noncomputable section

theorem markedPhysicalCoprimeScalarDetectorSum_congr_coefficients
    {J : Type*} [Fintype J] (P : J → Finset ℕ) (S T : Finset ℕ)
    (η : ℝ → ℂ) (Y : ℝ) (detector : ℤ → ℤ → ℤ → ℂ)
    {α α' β β' : ℕ → ℂ} (hα : ∀ m∈S,α m=α' m) (hβ : ∀ n∈T,β n=β' n) :
    markedPhysicalCoprimeScalarDetectorSum P S T η Y detector α β =
      markedPhysicalCoprimeScalarDetectorSum P S T η Y detector α' β' := by
  unfold markedPhysicalCoprimeScalarDetectorSum markedPhysicalScalarDetectorBlock
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro u hu
  obtain ⟨hvm,hvn⟩ := Finset.mem_product.mp hv
  obtain ⟨hum,hun⟩ := Finset.mem_product.mp hu
  simp only [markedPhysicalScalarDetectorTerm,markedPhysicalScalarCofactorTerm,
    hα _ hvm,hα _ hum,hβ _ hvn,hβ _ hun]

theorem markedPhysicalCoprimeScalarDetectorSum_restricted_coefficients
    {J : Type*} [Fintype J] (P : J → Finset ℕ) (S T : Finset ℕ)
    (η : ℝ → ℂ) (Y : ℝ) (detector : ℤ → ℤ → ℤ → ℂ)
    (W modulation : ℝ) (β ξ : ℕ → ℂ) :
    markedPhysicalCoprimeScalarDetectorSum P S T η Y detector
      (fun n => ξ n*markedMajorRestrictedCoefficient W modulation S n)
      (fun n => ξ n*markedPhysicalRestrictedBeta T β n)=
    markedPhysicalCoprimeScalarDetectorSum P S T η Y detector
      (fun n => ξ n*markedMajorCenteredCoefficient W modulation n) (fun n => ξ n*β n) := by
  apply markedPhysicalCoprimeScalarDetectorSum_congr_coefficients
  · intro m hm
    simp only [markedMajorRestrictedCoefficient,ite_eq_left hm]
  · intro n hn
    simp only [markedPhysicalRestrictedBeta,ite_eq_left hn]

end
end ArtinMatthews
