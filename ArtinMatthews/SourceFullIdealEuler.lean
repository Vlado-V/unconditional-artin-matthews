module

public import ArtinMatthews.SourceFullIdealFactorization
public import ArtinMatthews.SourceExteriorValueEuler
public import ArtinMatthews.FiniteSupportEuler
public import ArtinMatthews.VaryingKummerAnalyticDedekindSeriesClasses
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The extracted exterior factors agree with the literal full
Dedekind and ray Dirichlet series after deleting the exact finite set
S. All-prime convergence is derived from actual ideal factorization. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F]

theorem sourceFullPrimeEuler_hasProd_ideal (W : Ideal (𝓞 F) →*₀ ℂ)
    (hs : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} => ‖W I.val‖))
    (hp : ∀ P : ProbePrime F, ‖W P.asIdeal‖ < 1) :
    HasProd (fun P : ProbePrime F => (1 - W P.asIdeal)⁻¹)
      (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, W I.val) := by
  let E := sourceFullExponentIdealEquiv F
  let f (P : ProbePrime F) (n : ℕ) := W P.asIdeal ^ n
  have hf (e : ProbePrime F →₀ ℕ) : SourceEuler.finiteChoiceWeight f e = W (E e).val := by
    change (∏ P ∈ e.support, W P.asIdeal ^ e P) = W (sourceFullExponentIdeal F e)
    rw [sourceFullExponentIdeal, Finsupp.prod, map_prod]
    exact Finset.prod_congr rfl (fun P _ => (map_pow W P.asIdeal (e P)).symm)
  have hsum : Summable (fun e : ProbePrime F →₀ ℕ => ‖SourceEuler.finiteChoiceWeight f e‖) :=
    (hs.comp_injective E.injective).congr (fun e => congrArg norm (hf e).symm)
  have h := SourceEuler.finiteChoice_hasProd f (fun _ => pow_zero _) hsum
  have he : (∑' e : ProbePrime F →₀ ℕ, SourceEuler.finiteChoiceWeight f e) =
      ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, W I.val :=
    (tsum_congr hf).trans (E.tsum_eq (fun I => W I.val))
  rw [he] at h
  apply h.congr_fun
  intro P
  exact (hasSum_geometric_of_norm_lt_one (hp P)).tsum_eq.symm

theorem sourceFullRayEuler_hasProd {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)
    (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun P : ProbePrime F => (1 - sourcePrimeEulerRatio F P (η.allCoefficient P.asIdeal) s)⁻¹)
      (η.dirichlet s) := by
  let W := η.idealTerm hs
  have hp (P : ProbePrime F) : ‖W P.asIdeal‖ < 1 :=
    (sourcePrimeEulerRatio_norm_le_half F P (η.allCoefficient P.asIdeal) s
      (η.allCoefficient_norm_le_one _) hs.le).trans_lt (by norm_num)
  have he : (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, W I.val) = η.dirichlet s := by
    rw [η.dirichlet_eq_ideal_tsum hs]
    apply tsum_subtype_eq_of_support_subset
    intro I hi
    change I ≠ ⊥
    intro hI
    subst I
    exact hi (map_zero W)
  have h := sourceFullPrimeEuler_hasProd_ideal F W (η.idealTerm_summable_nonzero hs).norm hp
  rw [he] at h
  exact h

theorem sourceFullDedekindEuler_hasProd (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun P : ProbePrime F => (1 - sourcePrimeEulerRatio F P 1 s)⁻¹)
      (NumberField.dedekindZeta F s) := by
  let W : Ideal (𝓞 F) →*₀ ℂ :=
    (riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs)).comp Ideal.absNorm
  have hp (P : ProbePrime F) : ‖W P.asIdeal‖ < 1 := by
    change ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ < 1
    have h := sourcePrimeEulerRatio_norm_le_half F P 1 s (by simp) hs.le
    simpa only [sourcePrimeEulerRatio, one_mul] using h.trans_lt (by norm_num : (1 / 2 : ℝ) < 1)
  have hsum := HeckeIdealMobius.normSeries_summable F (show 0 < s.re - 1 by linarith)
  rw [show 1 + (s.re - 1) = s.re by ring] at hsum
  have hsumW : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} => ‖W I.val‖) := by
    apply hsum.congr
    intro I
    have hQ : (0 : ℝ) < Ideal.absNorm I.val := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
    change (Ideal.absNorm I.val : ℝ) ^ (-s.re) = ‖(Ideal.absNorm I.val : ℂ) ^ (-s)‖
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]
  let w (J : integralFractionalIdeals F) := ((FractionalIdeal.absNorm J.val.val : ℝ) : ℂ) ^ (-s)
  have hEq : (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, W I.val) = NumberField.dedekindZeta F s := by
    calc
      _ = ∑' I, w ((integralFractionalIdealsEquiv F) I) := by
        apply tsum_congr
        intro I
        change (Ideal.absNorm I.val : ℂ) ^ (-s) =
          ((FractionalIdeal.absNorm (I.val : FractionalIdeal (𝓞 F)⁰ F) : ℝ) : ℂ) ^ (-s)
        rw [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast, Complex.ofReal_natCast]
      _ = integralDedekindDirichlet F s := (integralFractionalIdealsEquiv F).tsum_eq w
      _ = _ := integralDedekindDirichlet_eq_dedekindZeta F hs
  have h := sourceFullPrimeEuler_hasProd_ideal F W hsumW hp
  rw [hEq] at h
  change HasProd (fun P : ProbePrime F => (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹)
    (NumberField.dedekindZeta F s) at h
  simpa only [sourcePrimeEulerRatio, one_mul] using h

end
end ArtinMatthews.SourceEulerAssembly
