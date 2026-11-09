module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Complex.Basic


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set Metric
open scoped ContDiff
noncomputable section

private def shiftedBilinearBumpCore : ContDiffBump (3/2 : ℝ) where
  rIn := 3/10
  rOut := 1/2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The fixed ratio-two bump with a closed inner plateau. -/
def shiftedBilinearUnitBump (x : ℝ) : ℂ := (shiftedBilinearBumpCore x : ℝ)

theorem shiftedBilinearUnitBump_smooth : ContDiff ℝ ∞ shiftedBilinearUnitBump :=
  Complex.ofRealCLM.contDiff.comp shiftedBilinearBumpCore.contDiff

theorem shiftedBilinearUnitBump_tsupport : tsupport shiftedBilinearUnitBump ⊆ Icc 1 2 := by
  have hs : tsupport shiftedBilinearUnitBump ⊆ tsupport (shiftedBilinearBumpCore : ℝ → ℝ) :=
    tsupport_comp_subset (g := Complex.ofReal) (by simp) _
  refine hs.trans ?_
  rw [shiftedBilinearBumpCore.tsupport_eq]
  intro x hx
  rw [mem_closedBall,Real.dist_eq,abs_le] at hx
  change -(1/2 : ℝ) ≤ x-3/2 ∧ x-3/2 ≤ 1/2 at hx
  exact ⟨by linarith [hx.1],by linarith [hx.2]⟩

theorem shiftedBilinearUnitBump_support : Function.support shiftedBilinearUnitBump ⊆ Icc 1 2 :=
  fun _ hx => shiftedBilinearUnitBump_tsupport (subset_tsupport _ hx)

theorem shiftedBilinearUnitBump_re_bounds (x : ℝ) :
    0 ≤ (shiftedBilinearUnitBump x).re ∧ (shiftedBilinearUnitBump x).re ≤ 1 :=
  ⟨shiftedBilinearBumpCore.nonneg,shiftedBilinearBumpCore.le_one⟩

theorem shiftedBilinearUnitBump_im_zero (x : ℝ) : (shiftedBilinearUnitBump x).im = 0 :=
  Complex.ofReal_im _

theorem shiftedBilinearUnitBump_one (x : ℝ) (hx : x ∈ Icc (6/5 : ℝ) (9/5)) :
    shiftedBilinearUnitBump x = 1 := by
  have hb : x ∈ closedBall (3/2 : ℝ) shiftedBilinearBumpCore.rIn := by
    rw [mem_closedBall,Real.dist_eq,abs_le]
    change -(3/10 : ℝ) ≤ x-3/2 ∧ x-3/2 ≤ 3/10
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  simp only [shiftedBilinearUnitBump,shiftedBilinearBumpCore.one_of_mem_closedBall hb,Complex.ofReal_one]

theorem shiftedBilinearUnitBump_derivative_bounds :
    ∃ Cg : ℕ → ℝ, (∀ j, 0 ≤ Cg j) ∧
      ∀ j x, ‖iteratedDeriv j shiftedBilinearUnitBump x‖ ≤ Cg j := by
  have hs (j : ℕ) : tsupport (iteratedDeriv j shiftedBilinearUnitBump) ⊆ Icc 1 2 := by
    induction j with
    | zero => simpa only [iteratedDeriv_zero] using shiftedBilinearUnitBump_tsupport
    | succ j ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih
  have hc (j : ℕ) : Continuous (iteratedDeriv j shiftedBilinearUnitBump) :=
    shiftedBilinearUnitBump_smooth.continuous_iteratedDeriv j (by simp)
  choose C hC using fun j => (isCompact_Icc : IsCompact (Icc (1 : ℝ) 2)).exists_bound_of_continuousOn
    (hc j).continuousOn
  refine ⟨fun j => max (C j) 0,fun _ => le_max_right _ _,?_⟩
  intro j x
  by_cases hx : x ∈ Icc (1 : ℝ) 2
  · exact (hC j x hx).trans (le_max_left _ _)
  · have hz : iteratedDeriv j shiftedBilinearUnitBump x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (hs j h))
    rw [hz,norm_zero]
    exact le_max_right _ _

def shiftedBilinearScaledBump (S x : ℝ) : ℂ := shiftedBilinearUnitBump (x/S)

theorem shiftedBilinearScaledBump_smooth (S : ℝ) : ContDiff ℝ ∞ (shiftedBilinearScaledBump S) :=
  shiftedBilinearUnitBump_smooth.comp (contDiff_id.div_const S)

theorem shiftedBilinearScaledBump_re_smooth (S : ℝ) :
    ContDiff ℝ ∞ (fun x => (shiftedBilinearScaledBump S x).re) :=
  Complex.reCLM.contDiff.comp (shiftedBilinearScaledBump_smooth S)

theorem shiftedBilinearScaledBump_re_bounds (S x : ℝ) :
    0 ≤ (shiftedBilinearScaledBump S x).re ∧ (shiftedBilinearScaledBump S x).re ≤ 1 :=
  shiftedBilinearUnitBump_re_bounds (x/S)

theorem shiftedBilinearScaledBump_ofReal_re (S x : ℝ) :
    ((shiftedBilinearScaledBump S x).re : ℂ) = shiftedBilinearScaledBump S x := by
  simp only [shiftedBilinearScaledBump,shiftedBilinearUnitBump,Complex.ofReal_re]

theorem shiftedBilinearScaledBump_support (S : ℝ) (hS : 0 < S) :
    Function.support (shiftedBilinearScaledBump S) ⊆ Icc S (2*S) := by
  intro x hx
  have h := shiftedBilinearUnitBump_support (show x/S ∈ Function.support shiftedBilinearUnitBump from hx)
  exact ⟨(one_le_div hS).mp h.1,(div_le_iff₀ hS).mp h.2⟩

theorem shiftedBilinearScaledBump_re_support (S : ℝ) (hS : 0 < S) :
    Function.support (fun x => (shiftedBilinearScaledBump S x).re) ⊆ Icc S (2*S) := by
  intro x hx
  apply shiftedBilinearScaledBump_support S hS
  intro h
  exact hx (by change (shiftedBilinearScaledBump S x).re = 0; rw [h,Complex.zero_re])

theorem shiftedBilinearScaledBump_tsupport (S : ℝ) (hS : 0 < S) :
    tsupport (shiftedBilinearScaledBump S) ⊆ Icc S (2*S) :=
  closure_minimal (shiftedBilinearScaledBump_support S hS) isClosed_Icc

theorem shiftedBilinearScaledBump_one (S x : ℝ) (hS : 0 < S)
    (hx : x ∈ Icc ((6/5)*S) ((9/5)*S)) : shiftedBilinearScaledBump S x = 1 :=
  shiftedBilinearUnitBump_one (x/S) ⟨(le_div_iff₀ hS).mpr hx.1,(div_le_iff₀ hS).mpr hx.2⟩

theorem shiftedBilinearScaledBump_derivative (S x : ℝ) (j : ℕ) :
    iteratedDeriv j (shiftedBilinearScaledBump S) x =
      (S⁻¹)^j • iteratedDeriv j shiftedBilinearUnitBump (x/S) := by
  have he : shiftedBilinearScaledBump S = fun y => shiftedBilinearUnitBump (S⁻¹*y) := by
    funext y
    simp only [shiftedBilinearScaledBump,div_eq_inv_mul]
  rw [he,iteratedDeriv_comp_const_smul (shiftedBilinearUnitBump_smooth.of_le (by simp)),div_eq_inv_mul]

theorem shiftedBilinearScaledBump_source_data :
    ∃ Cg : ℕ → ℝ, (∀ j, 0 ≤ Cg j) ∧ ∀ S : ℝ, 0 < S →
      ContDiff ℝ ∞ (shiftedBilinearScaledBump S) ∧
      Function.support (shiftedBilinearScaledBump S) ⊆ Icc S (2*S) ∧
      ∀ j x, ‖iteratedDeriv j (shiftedBilinearScaledBump S) x‖ ≤ Cg j/S^j := by
  obtain ⟨Cg,hCg,hb⟩ := shiftedBilinearUnitBump_derivative_bounds
  refine ⟨Cg,hCg,fun S hS => ⟨shiftedBilinearScaledBump_smooth S,
    shiftedBilinearScaledBump_support S hS,?_⟩⟩
  intro j x
  rw [shiftedBilinearScaledBump_derivative,norm_smul,
    Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hS.le) j)]
  calc
    _ ≤ (S⁻¹)^j*Cg j := mul_le_mul_of_nonneg_left (hb j (x/S)) (pow_nonneg (inv_nonneg.mpr hS.le) j)
    _ = _ := by rw [inv_pow,div_eq_inv_mul]

def shiftedBilinearMajorantScale1 (T : ℝ) : ℝ := 5*T/6

def shiftedBilinearMajorantScale2 (T : ℝ) : ℝ := 10*T/9

/-- A smooth majorant whose two summands have separate ratio-two supports. -/
def shiftedBilinearMajorant (T x : ℝ) : ℝ :=
  (shiftedBilinearScaledBump (shiftedBilinearMajorantScale1 T) x).re+
    (shiftedBilinearScaledBump (shiftedBilinearMajorantScale2 T) x).re

theorem shiftedBilinearMajorant_scales (T : ℝ) (hT : 2 ≤ T) :
    1 ≤ shiftedBilinearMajorantScale1 T ∧ 1 ≤ shiftedBilinearMajorantScale2 T ∧
      shiftedBilinearMajorantScale1 T ≤ T ∧ T ≤ shiftedBilinearMajorantScale2 T ∧
      shiftedBilinearMajorantScale2 T ≤ 2*T := by
  unfold shiftedBilinearMajorantScale1 shiftedBilinearMajorantScale2
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem shiftedBilinearMajorant_smooth (T : ℝ) : ContDiff ℝ ∞ (shiftedBilinearMajorant T) :=
  (shiftedBilinearScaledBump_re_smooth _).add (shiftedBilinearScaledBump_re_smooth _)

theorem shiftedBilinearMajorant_ofReal (T x : ℝ) :
    (shiftedBilinearMajorant T x : ℂ) =
      shiftedBilinearScaledBump (shiftedBilinearMajorantScale1 T) x+
        shiftedBilinearScaledBump (shiftedBilinearMajorantScale2 T) x := by
  simp only [shiftedBilinearMajorant,Complex.ofReal_add,shiftedBilinearScaledBump_ofReal_re]

theorem shiftedBilinearMajorant_bounds (T x : ℝ) :
    0 ≤ shiftedBilinearMajorant T x ∧ shiftedBilinearMajorant T x ≤ 2 := by
  have h₁ := shiftedBilinearUnitBump_re_bounds (x/shiftedBilinearMajorantScale1 T)
  have h₂ := shiftedBilinearUnitBump_re_bounds (x/shiftedBilinearMajorantScale2 T)
  exact ⟨add_nonneg h₁.1 h₂.1,(add_le_add h₁.2 h₂.2).trans_eq (by norm_num)⟩

theorem shiftedBilinearMajorant_ge_one (T x : ℝ) (hT : 0 < T) (hx : x ∈ Icc T (2*T)) :
    1 ≤ shiftedBilinearMajorant T x := by
  let S₁ := shiftedBilinearMajorantScale1 T
  let S₂ := shiftedBilinearMajorantScale2 T
  have hS₁ : 0 < S₁ := by dsimp [S₁,shiftedBilinearMajorantScale1]; positivity
  have hS₂ : 0 < S₂ := by dsimp [S₂,shiftedBilinearMajorantScale2]; positivity
  have h₁ := (shiftedBilinearUnitBump_re_bounds (x/S₁)).1
  have h₂ := (shiftedBilinearUnitBump_re_bounds (x/S₂)).1
  change 1 ≤ (shiftedBilinearScaledBump S₁ x).re+(shiftedBilinearScaledBump S₂ x).re
  by_cases h : x ≤ 3*T/2
  · have hx₁ : x ∈ Icc ((6/5)*S₁) ((9/5)*S₁) := by
      dsimp [S₁,shiftedBilinearMajorantScale1]
      exact ⟨by linarith [hx.1],by linarith⟩
    rw [shiftedBilinearScaledBump_one S₁ x hS₁ hx₁,Complex.one_re]
    exact le_add_of_nonneg_right h₂
  · have hx₂ : x ∈ Icc ((6/5)*S₂) ((9/5)*S₂) := by
      dsimp [S₂,shiftedBilinearMajorantScale2]
      exact ⟨by linarith [lt_of_not_ge h],by linarith [hx.2]⟩
    rw [shiftedBilinearScaledBump_one S₂ x hS₂ hx₂,Complex.one_re]
    exact le_add_of_nonneg_left h₁

theorem shiftedBilinearMajorant_tsupport (T : ℝ) (hT : 0 < T) :
    tsupport (shiftedBilinearMajorant T) ⊆ Icc (5*T/6) (20*T/9) := by
  have h₁ : 0 < shiftedBilinearMajorantScale1 T := by unfold shiftedBilinearMajorantScale1; positivity
  have h₂ : 0 < shiftedBilinearMajorantScale2 T := by unfold shiftedBilinearMajorantScale2; positivity
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra h
  have hz₁ : shiftedBilinearScaledBump (shiftedBilinearMajorantScale1 T) x = 0 := by
    by_contra hn
    have hm := shiftedBilinearScaledBump_support _ h₁ hn
    exact h ⟨hm.1,by dsimp [shiftedBilinearMajorantScale1] at hm; linarith [hm.2]⟩
  have hz₂ : shiftedBilinearScaledBump (shiftedBilinearMajorantScale2 T) x = 0 := by
    by_contra hn
    have hm := shiftedBilinearScaledBump_support _ h₂ hn
    exact h ⟨by dsimp [shiftedBilinearMajorantScale2] at hm; linarith [hm.1],
      by dsimp [shiftedBilinearMajorantScale2] at hm; linarith [hm.2]⟩
  exact hx (by simp only [shiftedBilinearMajorant,hz₁,hz₂,Complex.zero_re,add_zero])

end
end ArtinMatthews
