module

public import ArtinMatthews.SourceReflectionPositiveRetainedBranch
public import ArtinMatthews.SourceReflectionSignedExteriorProduct
public import ArtinMatthews.SourceReflectionFrozenWeights
public import ArtinMatthews.SourceReflectionActiveBranchReindex
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

/-! A branch missing a required digit vanishes at its literal inactive
Fourier coefficient. This applies on either side of the transformation. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil
open Finset
open scoped NumberField Classical BigOperators AdeleRing

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "S" => sourceHilbertSet K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "PE" => SourceExteriorPrime K S₀
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "active" => sourceReflectionActiveChoices K S₀
local notation "C" => sourceReflectionTameFourierCoefficient K hζ S₀

attribute [local instance] positiveTwistLabelFintype

private theorem missing_active_digit (e : E) {g : Finset PE} (hg : g ∈ e.support.powerset)
    (hg' : g ∉ active e) : ∃ P ∈ e.support, e P % 6 ≠ 0 ∧ P ∉ g := by
  have h : ¬ ∀ P ∈ e.support, e P % 6 ≠ 0 → P ∈ g :=
    fun h => hg' (mem_filter.mpr ⟨hg,h⟩)
  push Not at h
  exact h

theorem sourceReflectionInactiveDigitCoefficient_zero (P : PE) (n : ℕ) (hn : n % 6 ≠ 0) :
    C P (sourceReflectionPositiveIndex n) 0 = 0 := by
  rw [sourceReflectionTameFourierCoefficient_zero, ite_eq_right]
  intro h
  exact hn (congrArg Fin.val h)

theorem sourceReflectionPositiveTwistBranchFactor_eq_zero_off_activeChoice (e : E)
    {g : Finset PE} (hg : g ∈ e.support.powerset) (hg' : g ∉ active e)
    (x : sourceRing K S₀) :
    sourceReflectionPositiveTwistBranchFactor K hζ S₀ e g x = 0 := by
  obtain ⟨P,hP,hmod,hPg⟩ := missing_active_digit K S₀ e hg hg'
  let p : e.support := ⟨P,hP⟩
  unfold sourceReflectionPositiveTwistBranchFactor sourceReflectionPositiveTwistBranchFactorAt
  apply prod_eq_zero (mem_univ p)
  change (if P ∈ g then _ else C P (sourceReflectionPositiveIndex (e P)) 0) = 0
  rw [ite_eq_right hPg]
  exact sourceReflectionInactiveDigitCoefficient_zero K hζ S₀ P (e P) hmod

theorem sourceReflectionPositiveTwistBranch_eq_zero_off_activeChoice (e : E)
    {g : Finset PE} (hg : g ∈ e.support.powerset) (hg' : g ∉ active e)
    (W : Gf → ℂ) (qf : Gf) :
    sourceReflectionPositiveTwistBranch K hζ S₀ e g W qf = 0 := by
  obtain ⟨P,hP,hmod,hPg⟩ := missing_active_digit K S₀ e hg hg'
  let p : e.support := ⟨P,hP⟩
  unfold sourceReflectionPositiveTwistBranch
  apply sum_eq_zero
  intro u _
  split_ifs with hu
  · have hu₀ : u p = 0 := not_not.mp (fun hn => hPg ((hu p).mp hn))
    have hw : sourceReflectionPositiveTwistWeight K hζ S₀ e u = 0 := by
      unfold sourceReflectionPositiveTwistWeight
      apply prod_eq_zero (mem_univ p)
      change C P (sourceReflectionPositiveIndex (e P)) (u p) = 0
      rw [hu₀]
      exact sourceReflectionInactiveDigitCoefficient_zero K hζ S₀ P (e P) hmod
    rw [hw, zero_mul]
  · rfl

theorem sourceReflectionSignedExteriorProduct_eq_zero_off_activeChoice
    (hS : standardWeilBadPlaces K ⊆ S) (e : E)
    {g : Finset PE} (hg : g ∈ e.support.powerset) (hg' : g ∉ active e)
    (m : Kˣ) :
    sourceReflectionSignedExteriorProduct K S₀ hζ hS e g m = 0 := by
  obtain ⟨P,hP,hmod,hPg⟩ := missing_active_digit K S₀ e hg hg'
  apply sourceReflectionSignedExteriorProduct_eq_zero_of_local_zero K S₀ hζ hS e g m P
  rw [sourceReflectionSignedExteriorLocal_inactive K S₀ hζ hS P e g m hPg, ite_eq_left hP]
  change C P (sourceReflectionPositiveIndex (e P)) 0 * _ = 0
  rw [sourceReflectionInactiveDigitCoefficient_zero K hζ S₀ P (e P) hmod, zero_mul]

theorem sourceReflectionPositiveRetainedTwist_eq_sum_powerfulSimple
    (e : E) (R M : S → ℕ) (m : Kˣ) {T : ℝ} (hT : 1 ≤ T) (q₀ : Gf)
    (z : ∀ P : S, (P.val.adicCompletion K)ˣ) :
    sourceReflectionPositiveRetainedTwist K hζ S₀ e R M m hT q₀ z =
      ∑ f ∈ active (sourceReflectionPowerfulPart e),
        sourceReflectionPositiveRetainedBranch K hζ S₀ e (f ∪ (sourceReflectionSimplePart e).support)
          R M m hT q₀ z := by
  rw [← sourceReflectionPositiveRetainedBranch_sum_powerset]
  apply sourceReflectionActiveBranch_sum_powerfulSimple K S₀ e
  intro g hg hg'
  rw [sourceReflectionPositiveRetainedBranch_eq_finite]
  exact sourceReflectionPositiveTwistBranch_eq_zero_off_activeChoice K hζ S₀ e hg hg' _ _

end
end ArtinMatthews.SourceEulerAssembly
