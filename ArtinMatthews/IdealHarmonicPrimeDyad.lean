module

public import ArtinMatthews.MarkedRoughPrimeSlotCount
public import ArtinMatthews.WeightedIntervalDiscrepancy


set_option backward.privateInPublic true
@[expose] public section

/-! Actual reciprocal-prime cancellation on every sharp subinterval
of a dyad. The Dirichlet character is any nonprincipal character. -/
namespace ArtinMatthews
open Finset Filter MeasureTheory
open scoped Topology BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealHarmonicPrimeInterval {q : ℕ} (χ : DirichletCharacter ℂ q) (u v : ℝ) : ℂ :=
  ∑p∈(Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime,(p:ℂ)⁻¹*χ (p:ZMod q)

theorem idealReciprocal_lipschitz {H a b : ℝ} (hH : 0<H) (hHa : H≤a) :
    LipschitzOnWith (NNReal.mk ((H*H)⁻¹) (by positivity))
      (fun y : ℝ => ((y⁻¹:ℝ):ℂ)) (Set.Icc a b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  have hu0 : 0<u := hH.trans_le (hHa.trans hu.1)
  have hv0 : 0<v := hH.trans_le (hHa.trans hv.1)
  have he : u⁻¹-v⁻¹=(v-u)/(u*v) := by field_simp
  have hprod : H*H≤u*v := mul_le_mul (hHa.trans hu.1) (hHa.trans hv.1) hH.le hu0.le
  simp only [dist_eq_norm,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,NNReal.coe_mk]
  rw [he,abs_div,abs_of_pos (mul_pos hu0 hv0),abs_sub_comm]
  calc
    _ ≤ |u-v|/(H*H) := div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hH hH) hprod
    _ = _ := by ring

theorem idealHarmonicPrime_dyad (a P : ℝ) (ha : 0≤a) (hP : 0≤P) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ H : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (u v : ℝ),
        (q:ℝ)≤(Real.log H)^a → χ≠1 → H≤u → u≤v → v≤2*H →
        ‖idealHarmonicPrimeInterval χ u v‖≤C*(Real.log H)^(-P) := by
  obtain ⟨C,hC,hprime⟩ := marked_rough_prime_slot_siegel_walfisz a 2 1 P ha
    (by norm_num) (by norm_num) hP
  refine ⟨8*C,by positivity,?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually hprime,eventually_ge_atTop (2:ℝ)]
    with H hprime hH2
  intro q _ χ u v hq hχ hHu huv hvH
  have hH : 0<H := (by norm_num : (0:ℝ)<2).trans_le hH2
  have hL : 0<Real.log H := Real.log_pos (by linarith)
  have hu0 : 0<u := hH.trans_le hHu
  have hv0 : 0<v := hu0.trans_le huv
  have hupper : v≤Real.exp (2*Real.log H) := by
    rw [show 2*Real.log H=Real.log H+Real.log H by ring,Real.exp_add,Real.exp_log hH]
    nlinarith
  let c : ℕ→ℂ := fun n => if n.Prime then χ (n:ZMod q) else 0
  let φ : ℝ→ℂ := fun y => ((y⁻¹:ℝ):ℂ)
  let E := C*H*(Real.log H)^(-P)
  have hE : 0≤E := by dsimp [E]; positivity
  have hprefix (t : ℝ) (ht : t∈Set.Icc u v) :
      ‖(∑n∈Ioc ⌊u⌋₊ ⌊t⌋₊,c n)-∫y in u..t,(0:ℂ)‖≤E := by
    have hh := hprime q χ H u t hq (by rw [one_mul,Real.exp_log hH]) hHu ht.1
      (ht.2.trans hvH) (ht.2.trans hupper)
    simpa only [c,markedRoughPrimeIntervalSum,sum_filter,ite_eq_right hχ,
      sub_zero,intervalIntegral.integral_zero] using hh
  have hh := weightedIntervalDiscrepancy_bound c φ (fun _ : ℝ => (0:ℂ)) hu0.le huv hE
    (idealReciprocal_lipschitz hH hHu) intervalIntegrable_const hprefix
  have heq : (∑n∈Ioc ⌊u⌋₊ ⌊v⌋₊,φ n*c n)=idealHarmonicPrimeInterval χ u v := by
    rw [idealHarmonicPrimeInterval,sum_filter]
    apply sum_congr rfl
    intro n _
    by_cases hn : n.Prime
    · simp only [c,φ,ite_eq_left hn,Complex.ofReal_inv,Complex.ofReal_natCast]
    · simp only [c,ite_eq_right hn,mul_zero]
  rw [heq] at hh
  simp only [mul_zero,intervalIntegral.integral_zero,sub_zero] at hh
  have hφ : ‖φ v‖≤H⁻¹ := by
    simpa only [φ,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hv0)] using
      (inv_anti₀ hH (hHu.trans huv))
  have hd : ((H*H)⁻¹)*(v-u)≤H⁻¹ := by
    have hdiff : v-u≤H := by linarith
    calc
      _ ≤ ((H*H)⁻¹)*H := mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = _ := by field_simp
  have hcost : ‖φ v‖+((H*H)⁻¹)*(v-u)≤2*H⁻¹ := by linarith
  calc
    _ ≤ 4*E*(2*H⁻¹) := hh.trans (mul_le_mul_of_nonneg_left hcost (by positivity))
    _ = _ := by dsimp [E]; field_simp; ring

end
end ArtinMatthews
