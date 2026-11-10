module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealMultiplicativity
public import ArtinMatthews.VaryingKummerAnalyticHeckeIdealMobius
public import ArtinMatthews.QuadraticHeckeNormCoprime
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
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

/-- The genuine ray-character coefficient preserves absolute norm summability. -/
theorem quadraticHeckeCharacterNorm_summable {M : Ideal (𝓞 F)}
    (ψ : EvenIdealRayCharacter F M) (v : ℝ → ℂ) {X : ℝ}
    (hv : Summable (fun J : J₀ => ‖v ((Ideal.absNorm J.val : ℝ) / X)‖)) :
    Summable (fun J : J₀ =>
      ‖ψ.allCoefficient J.val * v ((Ideal.absNorm J.val : ℝ) / X)‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun J => ?_) hv
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ψ.allCoefficient_norm_le_one J.val)

/-- Coprimality gives a finite Möbius sum with the exact ray-character factor at each divisor. -/
theorem quadraticHeckeCharacterCoprimeNorm_reindex {M : Ideal (𝓞 F)}
    (ψ : EvenIdealRayCharacter F M) (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (v : ℝ → ℂ) {X : ℝ} (hX : 0 < X)
    (hv : Summable (fun J : J₀ => ‖v ((Ideal.absNorm J.val : ℝ) / X)‖)) :
    (∑' J : J₀, if IsCoprime J.val m then
      ψ.allCoefficient J.val * v ((Ideal.absNorm J.val : ℝ) / X) else 0) =
      ∑ d ∈ HeckeIdealMobius.divisors F m, (moebius d : ℂ) * ψ.allCoefficient d *
        ∑' J : J₀, ψ.allCoefficient J.val *
          v ((Ideal.absNorm J.val : ℝ) / (X / (Ideal.absNorm d : ℝ))) := by
  let f : Ideal (𝓞 F) → ℂ :=
    fun J => ψ.allCoefficient J * v ((Ideal.absNorm J : ℝ) / X)
  have hf₀ : f ⊥ = 0 := by simp [f]
  have hfsub : Summable (fun J : J₀ => f J.val) :=
    (quadraticHeckeCharacterNorm_summable F ψ v hv).of_norm
  have hf : Summable f := by
    have h := (summable_subtype_iff_indicator (f := f)
      (s := {J : Ideal (𝓞 F) | J ≠ ⊥})).mp hfsub
    apply h.congr
    intro J
    by_cases hJ : J = ⊥ <;> simp [Set.indicator, hJ, f]
  have hleft :
      (∑' J : J₀, if IsCoprime J.val m then
        ψ.allCoefficient J.val * v ((Ideal.absNorm J.val : ℝ) / X) else 0) =
      ∑' J : Ideal (𝓞 F), if IsCoprime J m then f J else 0 :=
    nonzeroIdeal_tsum F (fun J => if IsCoprime J m then f J else 0) (by simp [hf₀])
  rw [hleft, quadraticHeckeNorm_coprime_tsum F m hm f hf hf₀]
  apply Finset.sum_congr rfl
  intro d _
  rw [← nonzeroIdeal_tsum F (fun J => f (d * J)) (by simp [f])]
  calc
    _ = (moebius d : ℂ) * ∑' J : J₀,
        ψ.allCoefficient d * (ψ.allCoefficient J.val *
          v ((Ideal.absNorm J.val : ℝ) / (X / (Ideal.absNorm d : ℝ)))) := by
      congr 1
      apply tsum_congr
      intro J
      simp only [f, ψ.allCoefficient_mul, map_mul, Nat.cast_mul]
      have harg : ((Ideal.absNorm d : ℝ) * (Ideal.absNorm J.val : ℝ)) / X =
          (Ideal.absNorm J.val : ℝ) / (X / (Ideal.absNorm d : ℝ)) := by
        apply (div_eq_iff hX.ne').mpr
        rw [div_div_eq_mul_div, div_mul_cancel₀ _ hX.ne']
        exact mul_comm _ _
      rw [harg]
      ring
    _ = _ := by rw [tsum_mul_left]; ring

end
end ArtinMatthews
