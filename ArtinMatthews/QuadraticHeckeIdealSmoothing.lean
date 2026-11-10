module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealMultiplicativity
public import ArtinMatthews.VaryingKummerAnalyticRayIdealPrimitiveContinuation
public import ArtinMatthews.QuadraticHeckeNormSmoothing
public import ArtinMatthews.VaryingKummerAnalyticRayIdealEuler
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Complex Set MeasureTheory VaryingKummerAnalytic
open OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]

private theorem ideals_countable : Countable (Ideal (𝓞 K)) := by
  apply Set.countable_univ_iff.mp
  apply (Set.countable_iUnion (fun n : ℕ =>
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) n).countable)).mono
  intro J _
  exact mem_iUnion.mpr ⟨Ideal.absNorm J, by change Ideal.absNorm J ≤ Ideal.absNorm J; exact le_rfl⟩

/-- Mellin interchange on the absolutely convergent line for the actual
primitive continuation, indexed by the nonzero integral ideals. -/
theorem quadraticHeckeIdealSmoothing_contour {M : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
    (hprim : IsPrimitiveOnIdeals ψ.residue) (hnp : ψ.IsNonprincipal)
    (H : ℂ → ℂ) {σ : ℝ} (hσ : 1 < σ)
    (hHc : Continuous (fun t : ℝ => H ((σ : ℂ) + (t : ℂ) * I)))
    (hHi : Integrable (fun t : ℝ => H ((σ : ℂ) + (t : ℂ) * I)))
    {X : ℝ} (hX : 0 < X) :
    (∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥},
      ψ.allCoefficient J.val * mellinInv σ H ((Ideal.absNorm J.val : ℝ) / X)) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, (X : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I) * H ((σ : ℂ) + (t : ℂ) * I) *
          ψ.primitiveContinued hM hprim ((σ : ℂ) + (t : ℂ) * I) := by
  let : Countable (Ideal (𝓞 K)) := ideals_countable K
  let q (J : {J : Ideal (𝓞 K) // J ≠ ⊥}) : ℝ := Ideal.absNorm J.val
  have hq (J : {J : Ideal (𝓞 K) // J ≠ ⊥}) : 0 < q J := by
    change 0 < (Ideal.absNorm J.val : ℝ)
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr J.property)
  have hσ' : 1 < (σ : ℂ).re := by simpa using hσ
  have ha : Summable (fun J : {J : Ideal (𝓞 K) // J ≠ ⊥} => ‖ψ.allCoefficient J.val‖ * q J ^ (-σ)) := by
    refine (ψ.idealTerm_summable_nonzero hσ').norm.congr (fun J => ?_)
    rw [ψ.idealTerm_apply, norm_mul]
    have h := Complex.norm_cpow_eq_rpow_re_of_pos (hq J) (-(σ : ℂ))
    simpa only [q, Complex.ofReal_natCast, Complex.neg_re, Complex.ofReal_re] using
      congrArg (fun x => ‖ψ.allCoefficient J.val‖ * x) h
  rw [quadraticHeckeNormSmoothing_contour q hq (fun J => ψ.allCoefficient J.val) H σ hHc hHi ha hX]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hs : 1 < s.re := by simpa [s] using hσ
  change (X : ℂ) ^ s * H s * (∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥},
    ψ.allCoefficient J.val * (q J : ℂ) ^ (-s)) =
      (X : ℂ) ^ s * H s * ψ.primitiveContinued hM hprim s
  rw [ψ.primitiveContinued_eq_dirichlet hM hprim hnp hs, ψ.dirichlet_eq_ideal_tsum hs]
  congr 1
  calc
    _ = ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥}, ψ.idealTerm hs J.val := by
      apply tsum_congr
      intro J
      rw [ψ.idealTerm_apply]
      simp only [q, Complex.ofReal_natCast]
    _ = _ := by
      apply tsum_subtype_eq_of_support_subset
      intro J hJ h0
      apply hJ
      subst J
      exact map_zero _

end
end ArtinMatthews
