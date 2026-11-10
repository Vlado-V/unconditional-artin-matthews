module

public import ArtinMatthews.VaryingKummerAnalyticRayContinuation
public import ArtinMatthews.VaryingKummerAnalyticRayIdealEulerCorrection
public import ArtinMatthews.VaryingKummerAnalyticRayIdealPrimitiveContinuation
public import ArtinMatthews.VaryingKummerAnalyticRayPrimitiveEulerCorrection
public import ArtinMatthews.VaryingKummerAnalyticRayPrimitiveNonprincipal
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Convex.Contractible
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

/-! Exact analytic transfer from the original nonprincipal ray series to
its constructed primitive ideal-conductor continuation. The finite omitted
Euler factors are entire and nonzero in Re(s)>0, so zeros are preserved. -/
namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open NumberField RayClass IsDedekindDomain FractionalIdeal Set Module Filter Topology
open OAI.SevenEighths.FiniteFourier
open scoped BigOperators NumberField nonZeroDivisors Classical
namespace EvenRayCharacter
variable {K : Type*} [Field K] [NumberField K] {N : ℕ} [NeZero N]
variable (ψ : EvenRayCharacter K N) (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
variable (hMf : rationalModulusIdeal (𝓞 K) N ≤ f) (Ψ : EvenIdealRayCharacter K f)
variable (hprim : IsPrimitiveOnIdeals Ψ.residue)
variable (hagree : ∀ I : primeToModulusIdeals (rationalIdealRayModulus K N),
  Ψ.idealHom (I:FractionalIdealGroup K) = ψ.idealHom (I:FractionalIdealGroup K))
include hMf hagree

theorem nonprincipalContinued_eq_primitive_mul (hnp : ψ.IsNonprincipal) :
    ψ.nonprincipalContinued = fun s =>
      Ψ.primitiveContinued hf hprim s * Ψ.rationalBadEulerCorrection N s := by
  have hΨ := ψ.primitiveIdeal_isNonprincipal f hMf Ψ hagree hnp
  apply ((ψ.nonprincipalContinued_entire).differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    (((Ψ.primitiveContinued_entire hf hprim).mul
      (Ψ.rationalBadEulerCorrection_entire N)).differentiableOn.analyticOnNhd isOpen_univ)
    (z₀ := (2:ℂ))
  have h2 : (1:ℝ) < (2:ℂ).re := by norm_num
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h2] with s hs
  simp only [Pi.mul_apply]
  rw [ψ.nonprincipalContinued_eq_dirichlet hnp hs,
    Ψ.primitiveContinued_eq_dirichlet hf hprim hΨ hs]
  exact ψ.dirichlet_eq_primitive_correction f hMf Ψ hagree hs

theorem nonprincipalContinued_zero_iff_primitive (hnp : ψ.IsNonprincipal)
    {s : ℂ} (hs : 0 < s.re) :
    ψ.nonprincipalContinued s = 0 ↔ Ψ.primitiveContinued hf hprim s = 0 := by
  rw [congrFun (ψ.nonprincipalContinued_eq_primitive_mul f hf hMf Ψ hprim hagree hnp) s,
    mul_eq_zero]
  exact or_iff_left (Ψ.rationalBadEulerCorrection_ne_zero N hs)

omit hMf hagree in
theorem exists_primitive_analytic_transfer (hnp : ψ.IsNonprincipal) :
    ∃ (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
      (_hMf : rationalModulusIdeal (𝓞 K) N ≤ f) (Ψ : EvenIdealRayCharacter K f)
      (hprim : IsPrimitiveOnIdeals Ψ.residue),
      Ψ.IsNonprincipal ∧ f.absNorm ≤ (rationalModulusIdeal (𝓞 K) N).absNorm ∧
      (ψ.nonprincipalContinued = fun s =>
        Ψ.primitiveContinued hf hprim s * Ψ.rationalBadEulerCorrection N s) ∧
      ∀ s : ℂ, 0 < s.re →
        (ψ.nonprincipalContinued s = 0 ↔ Ψ.primitiveContinued hf hprim s = 0) := by
  obtain ⟨f,hf,hMf,Ψ,hprim,hΨ,hnorm,_,hagree⟩ :=
    ψ.exists_primitive_nonprincipal_idealCharacter hnp
  exact ⟨f,hf,hMf,Ψ,hprim,hΨ,hnorm,
    ψ.nonprincipalContinued_eq_primitive_mul f hf hMf Ψ hprim hagree hnp,
    fun _ hs => ψ.nonprincipalContinued_zero_iff_primitive f hf hMf Ψ hprim hagree hnp hs⟩

end EvenRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
