module

public import ArtinMatthews.SourceKPPhysicalBranch
public import ArtinMatthews.SourceKPPositivePhysicalRow
public import ArtinMatthews.SourceReflectionPositiveTwistBranchSupport
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

namespace ArtinMatthews
open NumberField IsDedekindDomain QuadraticWeil VaryingKummerAnalytic SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 12) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "Whole" => SWholeUnits K S
local notation "E" => SourcePrimeExponents K S₀
local notation "Mask" => sourceKPPositivePhysicalActiveMask K S₀

attribute [local instance] positiveTwistLabelFintype
variable {J : Ideal (𝓞 K)}

private theorem sourceKPPositivePhysicalActiveMask_sum (e : E)
    (h : SourceReflectionPositiveTwistLabels K S₀ e) :
    (∑ g ∈ e.support.powerset, Mask e g h) = 1 := by
  let g₀ := sourceReflectionPositiveTwistActiveSupport K S₀ e h
  have hg₀ : g₀ ∈ e.support.powerset := Finset.mem_powerset.mpr
    (sourceReflectionPositiveTwistActiveSupport_subset K S₀ e h)
  rw [Finset.sum_eq_single_of_mem g₀ hg₀]
  · exact ite_eq_left (fun P => (sourceReflectionPositiveTwistActiveSupport_mem K S₀ e h P).symm)
  · intro g hg hne
    apply ite_eq_right
    intro hh
    apply hne
    ext P
    by_cases hP : P ∈ e.support
    · exact (hh ⟨P,hP⟩).symm.trans
        ((sourceReflectionPositiveTwistActiveSupport_mem K S₀ e h ⟨P,hP⟩).symm)
    · exact iff_of_false (fun hgP => hP (Finset.mem_powerset.mp hg hgP))
        (fun hgP => hP (Finset.mem_powerset.mp hg₀ hgP))

theorem sourceKPPositivePhysicalRowValue_sum_branches
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    {T : ℝ} (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (e : E) (u : ExteriorUnitSixthClasses S) (x : Whole) :
    sourceKPPositivePhysicalRowValue K hζ S₀ hS η hJ hT p e u x =
      ∑ g ∈ e.support.powerset, sourceKPPositivePhysicalBranchValue K hζ S₀ hS η hJ hT p e u g x := by
  unfold sourceKPPositivePhysicalRowValue sourceKPPositivePhysicalBranchValue
    sourceKPPositivePhysicalFiniteValue sourceKPPhysicalResidualFiniteValue
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  unfold sourceKPPositivePhysicalTranslateWeight
  simp only [one_mul, mul_assoc]
  rw [← Finset.sum_mul, sourceKPPositivePhysicalActiveMask_sum K S₀ e i.1,one_mul]

end
end ArtinMatthews
