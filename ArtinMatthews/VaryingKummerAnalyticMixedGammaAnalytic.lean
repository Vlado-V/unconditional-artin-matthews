module

public import ArtinMatthews.VaryingKummerAnalyticMixedGammaProduct
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
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
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
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

/-! Holomorphy and nonvanishing of the actual mixed Gamma factor in Re(s)>0.
The half-plane uniqueness lemma is an exact generic OpenAI IdealThetaXi extract. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Set Filter
open scoped Classical BigOperators Topology
noncomputable section
lemma halfPlane_eq_of_real_eq {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {s | 1 < s.re})
    (hg : DifferentiableOn ℂ g {s | 1 < s.re})
    (hreal : ∀ s : ℝ, 1 < s → f s = g s) :
    EqOn f g {s | 1 < s.re} := by
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected {s : ℂ | 1 < s.re} :=
    ((convex_Ioi (1 : ℝ)).linear_preimage Complex.reCLM.toLinearMap).isPreconnected
  have him : Complex.ofReal '' Ioi (2 : ℝ) ⊆ {s : ℂ | f s = g s} \ {(2 : ℂ)} := by
    rintro z ⟨x, hx, rfl⟩
    have hx' : (2 : ℝ) < x := hx
    refine ⟨hreal x (lt_trans (by norm_num) hx'), ?_⟩
    simp only [mem_singleton_iff]
    intro H
    have HR := congrArg Complex.re H
    norm_num at HR
    linarith
  have hcl : (2 : ℂ) ∈ closure (Complex.ofReal '' Ioi (2 : ℝ)) := by
    have H : (2 : ℝ) ∈ closure (Ioi (2 : ℝ)) := by simp [closure_Ioi]
    simpa only [Complex.ofReal_ofNat] using mem_closure_image Complex.continuous_ofReal.continuousAt H
  exact (hf.analyticOnNhd hopen).eqOn_of_preconnected_of_mem_closure
    (hg.analyticOnNhd hopen) hconn (by norm_num) (closure_mono him hcl)


variable (K : Type*) [Field K] [NumberField K]

omit [NumberField K] in
theorem mixedGammaArgument_re_pos (w : InfinitePlace K) {s : ℂ} (hs : 0 < s.re) :
    0 < (((InfinitePlace.mult w : ℂ)*s/2).re) := by
  simpa using div_pos (mul_pos (Nat.cast_pos.mpr (InfinitePlace.mult_pos (w := w))) hs)
    (by norm_num : (0 : ℝ) < 2)

theorem mixedGammaFactor_ne_zero {s : ℂ} (hs : 0 < s.re) :
    mixedGammaFactor K s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro w _
  apply mul_ne_zero
  · exact mul_ne_zero (by norm_num) (Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  · exact Complex.Gamma_ne_zero_of_re_pos (mixedGammaArgument_re_pos K w hs)

theorem mixedGammaFactor_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mixedGammaFactor K) s := by
  have hg (w : InfinitePlace K) :
      DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma ((InfinitePlace.mult w : ℂ)*z/2)) s := by
    apply DifferentiableAt.comp s (Complex.differentiableAt_Gamma _ ?_) (by fun_prop)
    intro m he
    have hr := mixedGammaArgument_re_pos K w hs
    rw [he] at hr
    simp only [Complex.neg_re, Complex.natCast_re] at hr
    exact (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg m))) hr
  have hp (w : InfinitePlace K) : DifferentiableAt ℂ
      (fun z : ℂ => (Real.pi : ℂ)^(-((InfinitePlace.mult w : ℂ)*z/2))) s :=
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => -((InfinitePlace.mult w : ℂ)*z/2)) s).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  unfold mixedGammaFactor
  fun_prop

theorem mixedGammaFactor_differentiableOn :
    DifferentiableOn ℂ (mixedGammaFactor K) {s : ℂ | 0 < s.re} :=
  fun _ hs => (mixedGammaFactor_differentiableAt K hs).differentiableWithinAt

end
end ArtinMatthews.VaryingKummerAnalytic
