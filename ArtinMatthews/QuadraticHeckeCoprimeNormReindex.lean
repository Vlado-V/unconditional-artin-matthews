module

public import ArtinMatthews.VaryingKummerAnalyticHeckeIdealMobius
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.QuadraticHeckeNormCoprime
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

namespace ArtinMatthews
open NumberField Set MeasureTheory VaryingKummerAnalytic UniqueFactorizationMonoid
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
local notation "J₀" => {J : Ideal (𝓞 F) // J ≠ ⊥}

omit [NumberField F] in
private theorem nonzeroIdeal_tsum (f : Ideal (𝓞 F) → ℂ) (hf : f ⊥ = 0) :
    (∑' J : J₀, f J.val) = ∑' J : Ideal (𝓞 F), f J := by
  apply tsum_subtype_eq_of_support_subset
  intro J hJ hzero
  exact hJ (hzero ▸ hf)

/-- Coprimality in a genuine ideal norm sum becomes a finite sum of
unrestricted sums at the exact rescaled norm parameter. -/
theorem quadraticHeckeCoprimeNorm_reindex (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (v : ℝ → ℂ) {X : ℝ} (hX : 0 < X)
    (hv : Summable (fun J : J₀ => ‖v ((Ideal.absNorm J.val : ℝ) / X)‖)) :
    (∑' J : J₀, if IsCoprime J.val m then v ((Ideal.absNorm J.val : ℝ) / X) else 0) =
      ∑ d ∈ HeckeIdealMobius.divisors F m, (moebius d : ℂ) *
        ∑' J : J₀, v ((Ideal.absNorm J.val : ℝ) / (X / (Ideal.absNorm d : ℝ))) := by
  let f : Ideal (𝓞 F) → ℂ := fun J => if J = ⊥ then 0 else v ((Ideal.absNorm J : ℝ) / X)
  have hf₀ : f ⊥ = 0 := by simp [f]
  have hfsub : Summable (fun J : J₀ => f J.val) :=
    hv.of_norm.congr (fun J => by simp [f, J.property])
  have hf : Summable f := by
    have h := (summable_subtype_iff_indicator (f := f)
      (s := {J : Ideal (𝓞 F) | J ≠ ⊥})).mp hfsub
    apply h.congr
    intro J
    by_cases hJ : J = ⊥ <;> simp [Set.indicator, hJ, f]
  have hleft :
      (∑' J : J₀, if IsCoprime J.val m then v ((Ideal.absNorm J.val : ℝ) / X) else 0) =
        ∑' J : Ideal (𝓞 F), if IsCoprime J m then f J else 0 := by
    rw [← nonzeroIdeal_tsum F (fun J => if IsCoprime J m then f J else 0)
      (by simp [hf₀])]
    apply tsum_congr
    intro J
    simp [f, J.property]
  rw [hleft, quadraticHeckeNorm_coprime_tsum F m hm f hf hf₀]
  apply Finset.sum_congr rfl
  intro d hd
  have hd' : d ≠ ⊥ := by
    intro hd0
    have hdvd := (HeckeIdealMobius.mem_divisors F hm).1 hd
    obtain ⟨J, hJ⟩ := hdvd
    exact hm (by rw [hJ, hd0, Ideal.bot_mul])
  have hdn : (Ideal.absNorm d : ℝ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hd'
  congr 1
  rw [← nonzeroIdeal_tsum F (fun J => f (d * J)) (by simp [f])]
  apply tsum_congr
  intro J
  have hdJ : d * J.val ≠ ⊥ := mul_ne_zero hd' J.property
  simp only [f, ite_eq_right hdJ, map_mul, Nat.cast_mul]
  congr 1
  field_simp [hX.ne', hdn]

end
end ArtinMatthews
