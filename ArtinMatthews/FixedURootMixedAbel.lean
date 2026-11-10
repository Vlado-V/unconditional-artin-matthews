module

public import ArtinMatthews.FixedURootWeightedAbel
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.Basify
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


set_option backward.privateInPublic true
@[expose] public section

/-! Mixed smooth weights in two root coordinates. The proof keeps the
boundary, first-derivative and mixed-derivative contributions explicit. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators

theorem rootWeightVariation_le (f : ℝ → ℂ) {a b C : ℝ} (hab : a ≤ b)
    (hdf : Continuous (deriv f)) (hC : ∀ t ∈ Set.Icc a b, ‖deriv f t‖ ≤ C) :
    rootWeightVariation f a b ≤ ‖f a‖+(b-a)*C := by
  unfold rootWeightVariation
  apply add_le_add le_rfl
  rw [← intervalIntegral.integral_of_le hab]
  have h := intervalIntegral.integral_mono_on hab (hdf.norm.intervalIntegrable (μ := volume) a b)
    (intervalIntegrable_const (μ := volume)) hC
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using h

theorem root_weight_family_abel {ι : Type*} (S : Finset ι) (y : ι → ℝ)
    (w : ι → ℂ) (F : ι → ℝ → ℂ) {c d : ℝ} (hcd : c ≤ d)
    (hy : ∀ i ∈ S, y i ∈ Set.Icc c d)
    (hF : ∀ i, Differentiable ℝ (F i)) (hD : ∀ i, Continuous (deriv (F i))) :
    (∑ i ∈ S, w i*F i (y i)) = (∑ i ∈ S, w i*F i c) +
      ∫ s in c..d, ∑ i ∈ S, if s ≤ y i then w i*deriv (F i) s else 0 := by
  classical
  have hi (i : ι) : IntervalIntegrable
      (fun s => if s ≤ y i then w i*deriv (F i) s else 0) volume c d := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hcd).mpr
    have hh := (((continuous_const : Continuous (fun _ : ℝ => w i)).mul (hD i)).intervalIntegrable
      (μ := volume) c d).1.indicator (t := Set.Iic (y i)) measurableSet_Iic
    convert hh using 1
    ext s
    simp only [Set.indicator_apply, Set.mem_Iic, Pi.mul_apply]
  have hp (i : ι) (hiS : i ∈ S) :
      w i*F i (y i) = w i*F i c +
        ∫ s in c..d, if s ≤ y i then w i*deriv (F i) s else 0 := by
    have he : (fun s => if s ≤ y i then w i*deriv (F i) s else 0) =
        fun s => w i*(if s ≤ y i then deriv (F i) s else 0) := by
      funext s
      split_ifs <;> simp
    rw [he, intervalIntegral.integral_const_mul,
      root_weight_indicator_integral (F i) (hF i) (hD i) (hy i hiS)]
    ring
  rw [intervalIntegral.integral_finsetSum (fun i _ => hi i), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl hp

theorem root_weight_integral_family (F : ℝ → ℝ → ℂ)
    (hF : Continuous F.uncurry)
    (hFy : ∀ x, Differentiable ℝ (F x))
    (hDy : Continuous (fun p : ℝ × ℝ => deriv (F p.1) p.2))
    {a b c d : ℝ} (_hab : a ≤ b) (_hcd : c ≤ d) :
    (∫ x in a..b, ∫ y in c..d, F x y) =
      ((d-c : ℝ) : ℂ)*(∫ x in a..b, F x c) +
        ∫ s in c..d, (∫ x in a..b, deriv (F x) s)*((d-s : ℝ) : ℂ) := by
  let H : ℝ → ℝ → ℂ := fun x s => deriv (F x) s*((d-s : ℝ) : ℂ)
  have hH : Continuous H.uncurry :=
    hDy.mul (Complex.continuous_ofReal.comp (continuous_const.sub continuous_snd))
  have hI : IntegrableOn H.uncurry (Set.uIoc a b ×ˢ Set.uIoc c d) := by
    apply (hH.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
    exact Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc
  have hIc : Continuous (fun x => ∫ s in c..d, H x s) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hH c d
  have hFc : Continuous (fun x => F x c) := hF.comp (continuous_id.prodMk continuous_const)
  have hleft : IntervalIntegrable (fun x => ((d-c : ℝ) : ℂ)*F x c) volume a b :=
    (hFc.const_mul ((d-c : ℝ) : ℂ)).intervalIntegrable a b
  have hD (x : ℝ) : Continuous (deriv (F x)) :=
    hDy.comp (continuous_const.prodMk continuous_id)
  have hp (x : ℝ) : (∫ y in c..d, F x y) =
      ((d-c : ℝ) : ℂ)*F x c + ∫ s in c..d, H x s := by
    dsimp only [H]
    rw [root_weight_linear_integral (F x) (hFy x) (hD x)]
    ring
  calc
    _ = ∫ x in a..b, (((d-c : ℝ) : ℂ)*F x c + ∫ s in c..d, H x s) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact hp x
    _ = ((d-c : ℝ) : ℂ)*(∫ x in a..b, F x c) + ∫ x in a..b, ∫ s in c..d, H x s := by
      rw [intervalIntegral.integral_add hleft
        (hIc.intervalIntegrable a b), intervalIntegral.integral_const_mul]
    _ = ((d-c : ℝ) : ℂ)*(∫ x in a..b, F x c) + ∫ s in c..d, ∫ x in a..b, H x s := by
      rw [intervalIntegral_intervalIntegral_swap hI]
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s _
      exact intervalIntegral.integral_mul_const _ _

/-- A genuine mixed-C² rectangle estimate. Only the two boundary first
derivatives and the mixed derivative enter the error norm. -/
theorem root_weight_mixed_rectangle_error {ι : Type*}
    (S : Finset ι) (x y : ι → ℝ) (w : ι → ℂ) (F : ℝ → ℝ → ℂ) (ρ : ℂ)
    {a b c d E Cx Cy Cxy : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hE : 0 ≤ E)
    (hx : ∀ i ∈ S, x i ∈ Set.Icc a b) (hy : ∀ i ∈ S, y i ∈ Set.Icc c d)
    (hF : Continuous F.uncurry)
    (hFx : ∀ s, Differentiable ℝ (fun t => F t s))
    (hDx : ∀ s, Continuous (deriv (fun t => F t s)))
    (hFy : ∀ t, Differentiable ℝ (F t))
    (hDy : Continuous (fun p : ℝ × ℝ => deriv (F p.1) p.2))
    (hFxy : ∀ s, Differentiable ℝ (fun t => deriv (F t) s))
    (hDxy : ∀ s, Continuous (deriv (fun t => deriv (F t) s)))
    (hCx : ∀ t ∈ Set.Icc a b, ‖deriv (fun z => F z c) t‖ ≤ Cx)
    (hCy : ∀ s ∈ Set.Icc c d, ‖deriv (F a) s‖ ≤ Cy)
    (hCxy : ∀ t ∈ Set.Icc a b, ∀ s ∈ Set.Icc c d,
      ‖deriv (fun z => deriv (F z) s) t‖ ≤ Cxy)
    (hrect : ∀ t ∈ Set.Icc a b, ∀ s ∈ Set.Icc c d,
      ‖(∑ i ∈ S, if t ≤ x i ∧ s ≤ y i then w i else 0) -
        ρ*((b-t : ℝ) : ℂ)*((d-s : ℝ) : ℂ)‖ ≤ E) :
    ‖(∑ i ∈ S, w i*F (x i) (y i)) - ρ*(∫ t in a..b, ∫ s in c..d, F t s)‖ ≤
      E*(‖F a c‖+(b-a)*Cx+(d-c)*Cy+(b-a)*(d-c)*Cxy) := by
  classical
  let T (s : ℝ) := ∑ i ∈ S, if s ≤ y i then w i*deriv (F (x i)) s else 0
  let J (s : ℝ) := ∫ t in a..b, deriv (F t) s
  have hDi (t : ℝ) : Continuous (deriv (F t)) :=
    hDy.comp (continuous_const.prodMk continuous_id)
  have hJ : Continuous J := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hDy.comp continuous_swap
  have hi (i : ι) : IntervalIntegrable
      (fun s => if s ≤ y i then w i*deriv (F (x i)) s else 0) volume c d := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hcd).mpr
    have hh := (((continuous_const : Continuous (fun _ : ℝ => w i)).mul (hDi (x i))).intervalIntegrable
      (μ := volume) c d).1.indicator (t := Set.Iic (y i)) measurableSet_Iic
    convert hh using 1
    ext s
    simp only [Set.indicator_apply, Set.mem_Iic, Pi.mul_apply]
  have hT : IntervalIntegrable T volume c d := by
    convert IntervalIntegrable.sum S (fun i _ => hi i) using 1
    ext s
    simp only [T, Finset.sum_apply]
  have hR : IntervalIntegrable (fun s => ρ*J s*((d-s : ℝ) : ℂ)) volume c d :=
    ((hJ.const_mul ρ).mul (Complex.continuous_ofReal.comp (continuous_const.sub continuous_id))).intervalIntegrable c d
  have hprefix (s : ℝ) (hs : s ∈ Set.Icc c d) :
      ‖T s - ρ*J s*((d-s : ℝ) : ℂ)‖ ≤ E*(Cy+(b-a)*Cxy) := by
    have hh := root_weight_finite_error S x
      (fun i => if s ≤ y i then w i else 0) (fun t => deriv (F t) s)
      (ρ*((d-s : ℝ) : ℂ)) (E := E) hab hx (hFxy s) (hDxy s)
      (fun t ht => by
        simpa only [← ite_and, mul_assoc, mul_comm, mul_left_comm] using hrect t ht s hs)
    have hv : rootWeightVariation (fun t => deriv (F t) s) a b ≤ Cy+(b-a)*Cxy :=
      (rootWeightVariation_le _ hab (hDxy s) (fun t ht => hCxy t ht s hs)).trans
        (add_le_add (hCy s hs) le_rfl)
    apply le_trans _ (mul_le_mul_of_nonneg_left hv hE)
    convert hh using 1
    simp only [T, J, ite_mul, zero_mul]
    ring_nf
  have hbase : ‖(∑ i ∈ S, w i*F (x i) c) -
      ρ*((d-c : ℝ) : ℂ)*(∫ t in a..b, F t c)‖ ≤ E*(‖F a c‖+(b-a)*Cx) := by
    have hh := root_weight_finite_error S x w (fun t => F t c)
      (ρ*((d-c : ℝ) : ℂ)) (E := E) hab hx (hFx c) (hDx c) (fun t ht => by
        have hs : (∑ i ∈ S, if t ≤ x i ∧ c ≤ y i then w i else 0) =
            ∑ i ∈ S, if t ≤ x i then w i else 0 := by
          apply Finset.sum_congr rfl
          intro i hiS
          simp only [(hy i hiS).1, and_true]
        simpa only [hs, mul_assoc, mul_comm, mul_left_comm] using hrect t ht c ⟨le_rfl,hcd⟩)
    exact hh.trans (mul_le_mul_of_nonneg_left (rootWeightVariation_le _ hab (hDx c) hCx) hE)
  have hint : ‖∫ s in c..d, T s-ρ*J s*((d-s : ℝ) : ℂ)‖ ≤
      (E*(Cy+(b-a)*Cxy))*(d-c) := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => by
      have hs' : s ∈ Set.Ioc c d := by simpa only [Set.uIoc_of_le hcd] using hs
      exact hprefix s ⟨hs'.1.le,hs'.2⟩)).trans_eq
    rw [abs_of_nonneg (sub_nonneg.mpr hcd)]
  have heI : (∫ s in c..d, T s-ρ*J s*((d-s : ℝ) : ℂ)) =
      (∫ s in c..d, T s) - ρ*(∫ s in c..d, J s*((d-s : ℝ) : ℂ)) := by
    rw [intervalIntegral.integral_sub hT hR, ← intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    ring
  have he : (∑ i ∈ S, w i*F (x i) (y i)) - ρ*(∫ t in a..b, ∫ s in c..d, F t s) =
      ((∑ i ∈ S, w i*F (x i) c) - ρ*((d-c : ℝ) : ℂ)*(∫ t in a..b, F t c)) +
        ∫ s in c..d, T s-ρ*J s*((d-s : ℝ) : ℂ) := by
    rw [root_weight_family_abel S y w (fun i => F (x i)) hcd hy
      (fun i => hFy (x i)) (fun i => hDi (x i)),
      root_weight_integral_family F hF hFy hDy hab hcd, heI]
    dsimp only [T,J]
    ring
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hbase hint).trans_eq (by ring))

end ArtinMatthews
