module

public import ArtinMatthews.VaryingKummerAnalyticMixedMellinRegularization
public import ArtinMatthews.VaryingKummerAnalyticMixedContourZeros
public import ArtinMatthews.VaryingKummerAnalyticFinitePrincipalParts


set_option backward.privateInPublic true
@[expose] public section

/-! The exact finite explicit-formula rectangle, with the actual pole atone,
actual zero order atzero, and every actual completed-Dedekind zero inside. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Set Filter OAI.Ostmann
open OAI.PrimeDegreePackets.AnalyticGrowth
open scoped Classical Topology BigOperators Interval
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

omit [NumberField K] in
theorem mixedGammaArguments_right_of_minus_half {s : ℂ}
    (hs : -(1/2 : ℝ) ≤ s.re) (hs0 : s ≠ 0) :
    ∀ w : InfinitePlace K,∀ n : ℕ,(InfinitePlace.mult w : ℂ)*s/2 ≠ -(n : ℂ) := by
  intro w n he
  have hm : (0 : ℝ) < InfinitePlace.mult w := Nat.cast_pos.mpr (InfinitePlace.mult_pos (w := w))
  have hm2 : (InfinitePlace.mult w : ℝ) ≤ 2 := by
    unfold InfinitePlace.mult
    split_ifs <;> norm_num
  have hr := congrArg Complex.re he
  simp only [Complex.div_ofNat_re,Complex.mul_re,Complex.natCast_re,
    Complex.natCast_im,zero_mul,sub_zero,Complex.neg_re] at hr
  have hp : -(1/2 : ℝ) ≤ (InfinitePlace.mult w : ℝ)*s.re/2 := by
    nlinarith [mul_le_mul_of_nonneg_left hs hm.le]
  have hn : n=0 := by
    by_contra hn
    have hnn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    linarith
  subst n
  have hne : (InfinitePlace.mult w : ℂ)*s/2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt (InfinitePlace.mult_pos (w := w)))) hs0) (by norm_num)
  exact hne (by simpa using he)

variable (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
  (hpositive : tsupport f ⊆ Ioi 0) (hcontinuous : Continuous f)
  {x T : ℝ} (hx : 0<x) (hT : 0<T)
include hcompact hpositive hcontinuous hx hT

theorem mixedExplicitFormulaIntegrand_analytic_off_poles {s : ℂ}
    (hs : s ∈ uIcc (-(1/2 : ℝ)) 2 ×ℂ uIcc (-T) T)
    (hnot : s ∉ mixedContourPoles K T) :
    AnalyticAt ℂ (mixedExplicitFormulaIntegrand K f x) s := by
  have hs0 : s ≠ 0 := by intro h; apply hnot; simp [mixedContourPoles,h]
  have hs1 : s ≠ 1 := by intro h; apply hnot; simp [mixedContourPoles,h]
  have hsre : -(1/2 : ℝ) ≤ s.re := by
    have H := hs.1
    rw [uIcc_of_le (by norm_num)] at H
    exact H.1
  have hsim : |s.im| ≤ T := by
    have H := hs.2
    rw [uIcc_of_le (by linarith)] at H
    exact abs_le.mpr H
  have hxin : mixedCompletedDedekindXi K s ≠ 0 := by
    intro hz
    apply hnot
    simp only [mixedContourPoles,Finset.mem_insert]
    exact Or.inr (Or.inr ((mem_mixedContourZeros K T s).mpr ⟨hz,hsim⟩))
  have hzn := mixedDedekindZeta_ne_zero_away K hs0 hs1 hxin
    (mixedGammaArguments_right_of_minus_half K hsre hs0)
  have hza := mixedDedekindZeta_analyticAt K hs1
  have hlog : AnalyticAt ℂ (logDeriv (mixedDedekindZeta K)) s := hza.deriv.div hza hzn
  have hW := ((smoothMellin_entire f hcompact hpositive hcontinuous).mul
    (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne')))).analyticAt s
  exact hW.neg.mul hlog

/-- The exact actual finite contour identity. Only genuine geometric boundary
avoidance is required; all local residues and analytic continuation are proved. -/
theorem mixedMellin_rectangle_identity
    (havoid : ∀ ρ,mixedCompletedDedekindXi K ρ=0 → |ρ.im| ≠ T) :
    rectangleBoundaryIntegral (mixedExplicitFormulaIntegrand K f x) (-(1/2)) 2 (-T) T =
      (2*(Real.pi : ℂ)*I)*((x : ℂ)*mellin f 1 -
        ∑ ρ ∈ mixedContourZeros K T,
          (zeroMultiplicity (mixedCompletedDedekindXi K) ρ : ℂ)*mellin f ρ*(x : ℂ)^ρ -
        (((InfinitePlace.nrRealPlaces K : ℤ)+InfinitePlace.nrComplexPlaces K-1 : ℤ) : ℂ)*mellin f 0) := by
  let C : ℂ → ℂ := fun z => (mixedDedekindOrder K z : ℂ)*(mellin f z*(x : ℂ)^z)
  have H := rectangle_principal_parts (mixedExplicitFormulaIntegrand K f x) C
    (-(1/2)) 2 (-T) T (mixedContourPoles K T) (mixedContourPoles_inside K hT havoid)
    (mixedExplicitFormulaIntegrand_regular_part K f hcompact hpositive hcontinuous hx)
    (fun z hz hn => mixedExplicitFormulaIntegrand_analytic_off_poles K f hcompact
      hpositive hcontinuous hx hT hz hn)
  have hz0 : (0 : ℂ) ∉ insert 1 (mixedContourZeros K T) := by
    simp [zero_not_mem_mixedContourZeros K T]
  rw [mixedContourPoles,Finset.sum_insert hz0,
    Finset.sum_insert (one_not_mem_mixedContourZeros K T)] at H
  have hsum : (∑ z ∈ mixedContourZeros K T,C z) =
      ∑ z ∈ mixedContourZeros K T,
        (zeroMultiplicity (mixedCompletedDedekindXi K) z : ℂ)*mellin f z*(x : ℂ)^z := by
    apply Finset.sum_congr rfl
    intro z hz
    dsimp [C]
    rw [mixedDedekindOrder_xi_zero K ((mem_mixedContourZeros K T z).mp hz).1]
    ring
  rw [hsum] at H
  dsimp [C] at H
  rw [mixedDedekindOrder_zero,mixedDedekindOrder_one] at H
  simp only [cpow_zero,cpow_one,mul_one,Int.cast_neg,Int.cast_one,neg_one_mul] at H
  linear_combination H

end
end ArtinMatthews.VaryingKummerAnalytic
