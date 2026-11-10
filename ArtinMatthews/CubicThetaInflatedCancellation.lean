module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.MulChar.Basic
public import ArtinMatthews.CubicThetaUnitLiftNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-!
Norm-fiber cancellation after enlarging a finite residue modulus. The inflated
character is allowed to be nonzero on new nonunits of the larger ring.
-/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators Classical

/-- A cubic anticyclotomic residue character cancels against every function
of the norm after pullback along an arbitrary finite-ring quotient. -/
theorem anticyclotomic_cubic_inflated_sum_norm_eq_zero
    {R S : Type*} [CommRing R] [CommRing S] [Fintype R]
    (f : R →+* S) (hf : Function.Surjective f)
    (σR : R ≃+* R) (σS : S ≃+* S) (hσR : Function.Involutive σR)
    (hfσ : ∀ x, f (σR x) = σS (f x))
    (χ : MulChar S ℂ) (hχσ : ∀ u : Sˣ, χ (σS u) = (χ u)⁻¹)
    (hcubic : ∀ u : Sˣ, χ u ^ 3 = 1) (hne : χ ≠ 1) (F : R → ℂ) :
    (∑ x : R, χ (f x) * F (x * σR x)) = 0 := by
  have hχu : χ.toMonoidHom.comp (Units.coeHom S) ≠ 1 := by
    intro heq
    apply hne
    apply MulChar.ext
    intro v
    have hv := congrArg (fun ψ : Sˣ →* ℂ => ψ v) heq
    simpa using hv
  obtain ⟨u, huNorm, huχ⟩ := finite_ring_norm_one_unit_nontrivial
    f hf σR σS hσR hfσ χ.toMonoidHom hχσ hcubic hχu
  have hnorm (x : R) : ((u : R) * x) * σR ((u : R) * x) = x * σR x := by
    rw [map_mul]
    calc
      _ = ((u : R) * σR (u : R)) * (x * σR x) := by ac_rfl
      _ = _ := by rw [huNorm, one_mul]
  have ht := u.mulLeft.bijective.sum_comp (fun x : R => χ (f x) * F (x * σR x))
  change (∑ x : R, χ (f ((u : R) * x)) *
    F (((u : R) * x) * σR ((u : R) * x))) = _ at ht
  simp_rw [hnorm] at ht
  simp only [map_mul, mul_assoc, ← Finset.mul_sum] at ht
  have hp : (χ (f (u : R)) - 1) * (∑ x : R, χ (f x) * F (x * σR x)) = 0 := by
    linear_combination ht
  exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr huχ)

end ArtinMatthews
