module

public import ArtinMatthews.VaryingKummerAnalyticRayCharacter
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import ArtinMatthews.ArtinRayCompletedPower
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Actual finite-place power corrections of principal ideles. -/
noncomputable section
open scoped NumberField Classical
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
variable {K : Type*} [Field K] [NumberField K]

/-- A rational congruence modulo `D*n²` supplies an integral correction
idele whose `n`-th power cancels the prescribed bad-place components. -/
theorem exists_integral_power_correction
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (D n : ℕ) (hn : 0 < n)
    (hD : ∀ v ∈ S, (D : 𝓞 K) ∈ v.asIdeal)
    (a : 𝓞 K) (ha : a ≠ 0)
    (hc : a - 1 ∈ rationalModulusIdeal (𝓞 K) (D * n^2)) :
    ∃ B : IdeleGroup K, IdeleGroup.fractionalIdeal B = 1 ∧
      ∀ v ∈ S, IdeleGroup.finiteComponent v
        (IdeleGroup.principalIdele K
          (Units.mk0 (a : K) (by exact_mod_cast ha)) * B^n) = 1 := by
  choose r hr using fun v : ↥S =>
    completed_principal_exists_unit_pow v.1 D n hn (hD v.1 v.2) hc
  let u (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
      (v.adicCompletionIntegers K).units :=
    if h : v ∈ S then
      (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm (r ⟨v,h⟩)
    else 1
  let B : IdeleGroup K := (1, ⟨fun v => ((u v : (v.adicCompletion K)ˣ)⁻¹),
    Filter.Eventually.of_forall fun v =>
      (v.adicCompletionIntegers K).units.inv_mem (u v).property⟩)
  refine ⟨B, ?_, ?_⟩
  · apply MonoidHom.mem_ker.mp
    rw [IdeleGroup.fractionalIdeal_ker]
    intro v
    exact (v.adicCompletionIntegers K).units.inv_mem (u v).property
  · intro v hv
    apply Units.ext
    change ((a : K) : v.adicCompletion K) *
      (((u v : (v.adicCompletion K)ˣ)⁻¹ : (v.adicCompletion K)ˣ) :
        v.adicCompletion K)^n = 1
    have hroot : ((u v : (v.adicCompletion K)ˣ) : v.adicCompletion K)^n =
        ((a : K) : v.adicCompletion K) := by
      have h := congrArg (fun z : v.adicCompletionIntegers K =>
        (z : v.adicCompletion K)) (hr ⟨v,hv⟩)
      dsimp only [u]
      rw [dite_eq_left hv]
      change (((r ⟨v,hv⟩ : v.adicCompletionIntegers K) : v.adicCompletion K)^n) = _
      exact h
    rw [← hroot, ← mul_pow]
    simp

end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
end
