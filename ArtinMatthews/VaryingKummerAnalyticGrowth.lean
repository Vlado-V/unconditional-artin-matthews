module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Genuine generic Mellin growth estimates extracted from OpenAI
PrimePackets/MellinGrowth.lean and SubquadraticGrowth.lean. No number-field
signature or analytic-continuation hypothesis is assumed by these estimates. -/
namespace ArtinMatthews.ReusedGrowth
open MeasureTheory Set Filter Asymptotics
open scoped Topology Classical BigOperators
noncomputable section
lemma real_mellin_kernel_bound {c r t : ℝ} (hc : 0 < c) (hr : 0 < r)
    (ht : 0 < t) :
    r * Real.log t - c*t/2 ≤ r * Real.log (2*r/c) := by
  have hA : 0 < 2*r/c := by positivity
  have H := Real.log_le_sub_one_of_pos (div_pos ht hA)
  rw [Real.log_div (ne_of_gt ht) (ne_of_gt hA)] at H
  have H' := mul_le_mul_of_nonneg_left H hr.le
  have HE : r*(t/(2*r/c)) = c*t/2 := by field_simp
  rw [mul_sub, mul_sub, HE] at H'
  nlinarith

 

theorem mellin_norm_le {f : ℝ → ℂ} {c C r : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) (hr : 0 < r)
    (hzero : ∀ t, t ≤ 1 → f t = 0)
    (hbound : ∀ t, 1 < t → ‖f t‖ ≤ C * Real.exp (-c*t))
    (s : ℂ) (hs : s.re - 1 ≤ r) :
    ‖mellin f s‖ ≤ (2*C/c) * Real.exp (r * Real.log (2*r/c)) := by
  let A := Real.exp (r * Real.log (2*r/c))
  have Hpt (t : ℝ) (ht : 0 < t) :
      ‖(t:ℂ)^(s-1) * f t‖ ≤ C*A*Real.exp ((-c/2)*t) := by
    by_cases ht1 : 1 < t
    · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
        Complex.sub_re, Complex.one_re]
      calc
        _ ≤ t^(s.re-1)*(C*Real.exp (-c*t)) :=
          mul_le_mul_of_nonneg_left (hbound t ht1) (Real.rpow_nonneg ht.le _)
        _ ≤ t^r*(C*Real.exp (-c*t)) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le ht1.le hs) (by positivity)
        _ = C * Real.exp (r*Real.log t-c*t) := by
          rw [Real.rpow_def_of_pos ht, show r*Real.log t-c*t = Real.log t*r + (-c*t) by ring, Real.exp_add]
          ring
        _ ≤ C * Real.exp (r*Real.log (2*r/c) + (-c/2)*t) := by
          apply mul_le_mul_of_nonneg_left _ hC
          apply Real.exp_le_exp.mpr
          have H := real_mellin_kernel_bound hc hr ht
          linarith
        _ = _ := by rw [Real.exp_add]; dsimp [A]; ring
    · rw [hzero t (le_of_not_gt ht1), mul_zero, norm_zero]
      positivity
  unfold mellin
  simp only [smul_eq_mul]
  calc
    _ ≤ ∫ t in Ioi (0:ℝ), C*A*Real.exp ((-c/2)*t) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_exp_mul_Ioi (by linarith : -c/2 < 0) 0).const_mul (C*A))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Hpt t ht
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -c/2 < 0)]
      simp only [mul_zero, Real.exp_zero]
      dsimp [A]
      field_simp






 
def HasSubquadraticGrowth (f : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ R : ℝ in atTop, ∀ z : ℂ,
    ‖z‖ ≤ R → ‖f z‖ ≤ Real.exp (ε * R^2)

lemma eventually_const_le_exp_quad {ε : ℝ} (hε : 0 < ε) (B : ℝ) :
    ∀ᶠ R : ℝ in atTop, B ≤ Real.exp (ε*R^2) :=
  (Real.tendsto_exp_atTop.comp (tendsto_const_mul_pow_atTop (by decide : (2:ℕ) ≠ 0)
    hε)).eventually_ge_atTop B

lemma hasSubquadraticGrowth_const (c : ℂ) : HasSubquadraticGrowth (fun _ => c) := by
  intro ε hε
  filter_upwards [eventually_const_le_exp_quad hε ‖c‖] with R hR
  exact fun _ _ => hR

lemma HasSubquadraticGrowth.of_bound {f : ℂ → ℂ} {B : ℝ → ℝ}
    (hB : Tendsto (fun R => B R / R^2) atTop (𝓝 0))
    (hf : ∀ᶠ R : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ Real.exp (B R)) :
    HasSubquadraticGrowth f := by
  intro ε hε
  filter_upwards [hf, hB.eventually (gt_mem_nhds hε), eventually_gt_atTop (0:ℝ)]
    with R hR hBR hRp
  intro z hz
  apply (hR z hz).trans
  apply Real.exp_le_exp.mpr
  exact ((div_lt_iff₀ (sq_pos_of_pos hRp)).mp hBR).le

lemma HasSubquadraticGrowth.add {f g : ℂ → ℂ}
    (hf : HasSubquadraticGrowth f) (hg : HasSubquadraticGrowth g) :
    HasSubquadraticGrowth (fun z => f z + g z) := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity), hg (ε/2) (by positivity),
    eventually_const_le_exp_quad (by positivity : 0 < ε/2) 2] with R hR hS hT
  intro z hz
  calc
    _ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ 2*Real.exp ((ε/2)*R^2) := by linarith [hR z hz, hS z hz]
    _ ≤ Real.exp ((ε/2)*R^2)*Real.exp ((ε/2)*R^2) :=
      mul_le_mul_of_nonneg_right hT (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma HasSubquadraticGrowth.mul {f g : ℂ → ℂ}
    (hf : HasSubquadraticGrowth f) (hg : HasSubquadraticGrowth g) :
    HasSubquadraticGrowth (fun z => f z * g z) := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity), hg (ε/2) (by positivity)] with R hR hS
  intro z hz
  calc
    _ = ‖f z‖*‖g z‖ := norm_mul _ _
    _ ≤ Real.exp ((ε/2)*R^2)*Real.exp ((ε/2)*R^2) :=
      mul_le_mul (hR z hz) (hS z hz) (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma HasSubquadraticGrowth.neg {f : ℂ → ℂ} (hf : HasSubquadraticGrowth f) :
    HasSubquadraticGrowth (fun z => -f z) := by
  simpa only [neg_mul, one_mul] using (hasSubquadraticGrowth_const (-1)).mul hf

lemma HasSubquadraticGrowth.sub {f g : ℂ → ℂ}
    (hf : HasSubquadraticGrowth f) (hg : HasSubquadraticGrowth g) :
    HasSubquadraticGrowth (fun z => f z - g z) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma HasSubquadraticGrowth.finset_sum {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ S, HasSubquadraticGrowth (f i)) :
    HasSubquadraticGrowth (fun z => ∑ i ∈ S, f i z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hasSubquadraticGrowth_const 0
  | @insert i S hi IH =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self _ _)).add (IH (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma HasSubquadraticGrowth.comp_affine {f : ℂ → ℂ} (hf : HasSubquadraticGrowth f)
    (a b : ℂ) : HasSubquadraticGrowth (fun z => f (a*z+b)) := by
  let A : ℝ := ‖a‖ + ‖b‖ + 1
  have hA : 0 < A := by dsimp [A]; positivity
  intro ε hε
  have H := (Tendsto.const_mul_atTop hA tendsto_id).eventually
    (hf (ε/A^2) (by positivity))
  filter_upwards [H, eventually_ge_atTop (1:ℝ)] with R hR hRp
  intro z hz
  have hzz : ‖a*z+b‖ ≤ A*R := by
    calc
      _ ≤ ‖a*z‖+‖b‖ := norm_add_le _ _
      _ = ‖a‖*‖z‖+‖b‖ := by rw [norm_mul]
      _ ≤ A*R := by dsimp [A]; nlinarith [mul_le_mul_of_nonneg_left hz (norm_nonneg a), norm_nonneg b]
  have HE : ε/A^2*(A*R)^2 = ε*R^2 := by field_simp
  simpa only [id_eq, HE] using hR (a*z+b) hzz

lemma tendsto_mellin_bound {a : ℝ} (ha : 0 < a) (k : ℝ) :
    Tendsto (fun R : ℝ => (k+(R+1)*Real.log (a*(R+1)))/R^2) atTop (𝓝 0) := by
  have HR : Tendsto (fun R : ℝ => R+1) atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_id
  have HI : Tendsto (fun R : ℝ => (R+1)/R) atTop (𝓝 1) := by
    have H := (tendsto_const_nhds (x := (1:ℝ))).add (tendsto_inv_atTop_zero : Tendsto (fun R:ℝ => R⁻¹) _ _)
    apply (show Tendsto (fun R : ℝ => 1+R⁻¹) atTop (𝓝 (1:ℝ)) by simpa using H).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    field_simp
  have HL0 : Tendsto (fun R : ℝ => Real.log R / R) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have HL : Tendsto (fun R : ℝ => Real.log (a*(R+1))/(R+1)) atTop (𝓝 0) := by
    have H := (tendsto_const_nhds.div_atTop HR (a := Real.log a)).add (HL0.comp HR)
    apply (show Tendsto (fun R : ℝ => Real.log a/(R+1)+Real.log (R+1)/(R+1))
      atTop (𝓝 0) by simpa using H).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    rw [Real.log_mul (ne_of_gt ha) (by positivity : R+1 ≠ 0), add_div]
  have HK : Tendsto (fun R : ℝ => k/R^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0))
  have H := HK.add ((HI.pow 2).mul HL)
  apply (show Tendsto (fun R : ℝ => k/R^2+((R+1)/R)^2*(Real.log (a*(R+1))/(R+1)))
    atTop (𝓝 0) by simpa using H).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  field_simp

 

theorem mellin_hasSubquadraticGrowth {f : ℝ → ℂ} {c C : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) (hzero : ∀ t, t ≤ 1 → f t = 0)
    (hbound : ∀ t, 1 < t → ‖f t‖ ≤ C*Real.exp (-c*t)) :
    HasSubquadraticGrowth (mellin f) := by
  apply HasSubquadraticGrowth.of_bound (tendsto_mellin_bound (by positivity : 0 < 2/c) (2*C/c))
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
  intro z hz
  have H := mellin_norm_le hc hC (by linarith : 0 < R+1) hzero hbound z
    (by linarith [Complex.re_le_norm z] : z.re-1 ≤ R+1)
  calc
    _ ≤ (2*C/c)*Real.exp ((R+1)*Real.log ((2/c)*(R+1))) := by
      simpa only [div_mul_eq_mul_div] using H
    _ ≤ Real.exp (2*C/c) * Real.exp ((R+1)*Real.log ((2/c)*(R+1))) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      linarith [Real.add_one_le_exp (2*C/c)]
    _ = _ := by rw [← Real.exp_add]


lemma tendsto_affine_div_sq (a b : ℝ) :
    Tendsto (fun R : ℝ => (a*R+b)/R^2) atTop (𝓝 0) := by
  have H1 : Tendsto (fun R : ℝ => a/R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have H2 : Tendsto (fun R : ℝ => b/R^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0))
  apply (show Tendsto (fun R : ℝ => a/R+b/R^2) atTop (𝓝 0) by simpa using H1.add H2).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  field_simp

lemma hasSubquadraticGrowth_id : HasSubquadraticGrowth (fun z => z) := by
  apply HasSubquadraticGrowth.of_bound (by simpa using tendsto_affine_div_sq 1 0)
  apply Filter.Eventually.of_forall
  intro R z hz
  exact hz.trans (by linarith [Real.add_one_le_exp R])

lemma hasSubquadraticGrowth_exp_affine (a b : ℂ) :
    HasSubquadraticGrowth (fun z => Complex.exp (a*z+b)) := by
  apply HasSubquadraticGrowth.of_bound (tendsto_affine_div_sq ‖a‖ ‖b‖)
  apply Filter.Eventually.of_forall
  intro R z hz
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ‖a*z+b‖ := Complex.re_le_norm _
    _ ≤ ‖a*z‖+‖b‖ := norm_add_le _ _
    _ ≤ ‖a‖*R+‖b‖ := by rw [norm_mul]; gcongr

lemma hasSubquadraticGrowth_const_cpow {a : ℝ} (ha : 0 < a) :
    HasSubquadraticGrowth (fun z : ℂ => (a:ℂ)^z) := by
  simpa only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne'), add_zero]
    using hasSubquadraticGrowth_exp_affine (Complex.log (a:ℂ)) 0

lemma HasSubquadraticGrowth.congr {f g : ℂ → ℂ} (hf : HasSubquadraticGrowth f)
    (h : ∀ z, f z = g z) : HasSubquadraticGrowth g := by
  have : f = g := funext h
  rwa [← this]

lemma HasSubquadraticGrowth.pow {f : ℂ → ℂ} (hf : HasSubquadraticGrowth f) (n : ℕ) :
    HasSubquadraticGrowth (fun z => f z ^ n) := by
  induction n with
  | zero => simpa using hasSubquadraticGrowth_const 1
  | succ n IH => simpa only [pow_succ] using IH.mul hf

end
end ArtinMatthews.ReusedGrowth
