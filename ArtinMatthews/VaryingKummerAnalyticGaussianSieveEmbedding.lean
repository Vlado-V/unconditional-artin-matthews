module

public import ArtinMatthews.VaryingKummerAnalyticGaussianSieveScale
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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


set_option backward.privateInPublic true
@[expose] public section

/-! Transport of the actual coordinate sieve along an injective integer
coordinate map, with exact preservation of the coefficient energy. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open scoped BigOperators
noncomputable section
variable {β ι α : Type*} [Fintype β]

theorem coordinate_modular_primal_sieve_embedding {Q H : ℝ} (hQ : 1 ≤ Q) (hH : 0 < H)
    (P : Finset ι) (x : ι → β → ℝ)
    (hsep : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → ∀ k : β → ℤ,
      1/Q ≤ ‖(fun b => x i b-x j b+(k b:ℝ))‖)
    (N : Finset α) (n : α → β → ℤ) (hn : Function.Injective n)
    (hN : ∀ a ∈ N, (∑ b, (n a b:ℝ)^2) ≤ H^2) (v : α → ℂ) :
    (∑ p ∈ P, ‖∑ a ∈ N, v a*coordinatePhase (x p) (n a)‖^2) ≤
      (coordinateOptimizedSieveConstant β*(H^(Fintype.card β)+Q^(Fintype.card β)))*
        ∑ a ∈ N, ‖v a‖^2 := by
  classical
  let w := Function.extend n v (fun _ => 0)
  have hsupport : ∀ k ∈ N.image n, (∑ b, (k b:ℝ)^2) ≤ H^2 := by
    intro k hk
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hk
    exact hN a ha
  have hs := coordinate_modular_primal_sieve_optimized hQ hH P x hsep (N.image n) hsupport w
  simpa only [Finset.sum_image hn.injOn,w,hn.extend_apply] using hs

end
end ArtinMatthews.VaryingKummerAnalytic
