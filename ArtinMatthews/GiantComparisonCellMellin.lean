module

public import ArtinMatthews.GiantComparisonCircleTransfer
public import ArtinMatthews.GiantPhysicalMellinBound


set_option backward.privateInPublic true
@[expose] public section

/-! Mellin separation of the actual product-shift comparison keeps
the smooth cutoff and all four endpoint and free-label phases. -/
namespace ArtinMatthews
open MeasureTheory AddCircle Finset
open scoped BigOperators ComplexConjugate FourierTransform ContDiff SchwartzMap
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]

def giantComparisonNatCutoffSum (P : I → Finset ℕ) (R : K → Finset ℕ)
    (f : IdealSelectedLabels P → ℂ) (g : IdealSelectedLabels R → ℂ)
    (S T : Finset ℕ) (U V : ℕ → ℂ) (Ψ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ a, (idealSelectedMass P a : ℂ)*f a *
    ∑ b, (idealSelectedMass R b : ℂ)*g b *
      ∑ w ∈ S, ∑ v ∈ T, if v = w+idealSelectedProduct a*idealSelectedProduct b then
        conj (U w)*V v*Ψ ((w : ℝ)/(x*((idealSelectedProduct a*idealSelectedProduct b : ℕ) : ℝ)))
      else 0

private theorem comparison_mellin_phase_mul (u : ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    primeExtractionMellinPhase u (s*t) =
      primeExtractionMellinPhase u s * primeExtractionMellinPhase u t := by
  unfold primeExtractionMellinPhase
  rw [Real.log_mul hs.ne' ht.ne', ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem giantComparisonNatShiftSum_norm_le_sqrt (P : I → Finset ℕ) (R : K → Finset ℕ)
    (hP : ∀ i, 0 < bandReciprocalMass (P i)) (hR : ∀ j, 0 < bandReciprocalMass (R j))
    (f : IdealSelectedLabels P → ℂ) (g : IdealSelectedLabels R → ℂ)
    (hf : ∀ a, ‖f a‖ ≤ 1) (hg : ∀ b, ‖g b‖ ≤ 1)
    (S T : Finset ℕ) (U V : ℕ → ℂ) :
    ‖giantComparisonNatShiftSum P R f g S T U V‖ ≤
      Real.sqrt ((∑ w ∈ S, ‖U w‖^2)*(∑ v ∈ T, ‖V v‖^2)) := by
  have h := giantComparisonNatShiftSum_norm_le P R hP hR f g hf hg S T U V
    (Q := 1) (ρ := 0) (δ := 1) (δarc := 0) le_rfl zero_le_one zero_le_one le_rfl
    (fun t _ _ => giantComparisonMultiplier_norm_le_one P R hP hR f g hf hg (-t))
    (fun r _ => by simp)
  simpa only [one_mul, mul_zero, Real.sqrt_zero, add_zero] using h

private theorem comparison_cell_sum {A B : Type*} (P : Finset A) (R : Finset B)
    (S T : Finset ℕ) (F : A × B × ℕ × ℕ → ℂ) :
    (∑ e ∈ P ×ˢ (R ×ˢ (S ×ˢ T)), F e) =
      ∑ a ∈ P, ∑ b ∈ R, ∑ w ∈ S, ∑ v ∈ T, F (a,b,w,v) := by
  rw [Finset.sum_product]
  apply sum_congr rfl
  intro a _
  rw [Finset.sum_product]
  apply sum_congr rfl
  intro b _
  rw [Finset.sum_product]

theorem giantComparisonNatCutoffSum_mellin_bound (P : I → Finset ℕ) (R : K → Finset ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime) (hR : ∀ j p, p ∈ R j → p.Prime)
    (hVP : ∀ i, 0 < bandReciprocalMass (P i)) (hVR : ∀ j, 0 < bandReciprocalMass (R j))
    (f : IdealSelectedLabels P → ℂ) (g : IdealSelectedLabels R → ℂ)
    (hf : ∀ a, ‖f a‖ ≤ 1) (hg : ∀ b, ‖g b‖ ≤ 1)
    (S T : Finset ℕ) (U V : ℕ → ℂ) (hS : ∀ w ∈ S, 0 < w)
    (Ψ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a) (hsupp : Function.support Ψ ⊆ Set.Icc a b)
    (hΨ : ContDiff ℝ ∞ Ψ) {x W B : ℝ} (hx : 0 < x) (hW : 0 < W) (hB : 0 ≤ B)
    (n : ℕ)
    (hbound : ∀ t ∈ Set.Icc (-W) W,
      ‖giantComparisonNatShiftSum P R
        (fun u => f u*primeExtractionMellinPhase (-t) (idealSelectedProduct u))
        (fun v => g v*primeExtractionMellinPhase (-t) (idealSelectedProduct v))
        S T (fun w => U w*primeExtractionMellinPhase (-t) (w : ℝ)) V‖ ≤ B) :
    ‖giantComparisonNatCutoffSum P R f g S T U V Ψ x‖ ≤
      (∫ t : ℝ, ‖(𝓕 (primeExtractionLogProfile Ψ ha hsupp hΨ)) t‖)*B +
        ((∫ t : ℝ, |t|^n*‖(𝓕 (primeExtractionLogProfile Ψ ha hsupp hΨ)) t‖)/W^n) *
          Real.sqrt ((∑ w ∈ S, ‖U w‖^2)*(∑ v ∈ T, ‖V v‖^2)) := by
  let E := IdealSelectedLabels P × IdealSelectedLabels R × ℕ × ℕ
  let edges : Finset E := univ ×ˢ (univ ×ˢ (S ×ˢ T))
  let w (e : E) := e.2.2.1
  let v (e : E) := e.2.2.2
  let d (e : E) := idealSelectedProduct e.1*idealSelectedProduct e.2.1
  let C (e : E) : ℂ := if v e = w e+d e then
    (idealSelectedMass P e.1 : ℂ)*f e.1*(idealSelectedMass R e.2.1 : ℂ)*g e.2.1*conj (U (w e))*V (v e)
    else 0
  have hw (e : E) (he : e ∈ edges) : 0 < (w e : ℝ) :=
    Nat.cast_pos.mpr (hS _ (mem_product.mp (mem_product.mp (mem_product.mp he).2).2).1)
  have hp (u : IdealSelectedLabels P) : 0 < (idealSelectedProduct u : ℝ) :=
    Nat.cast_pos.mpr (idealSelectedProduct_pos hP u)
  have hr (u : IdealSelectedLabels R) : 0 < (idealSelectedProduct u : ℝ) :=
    Nat.cast_pos.mpr (idealSelectedProduct_pos hR u)
  have hd (e : E) (_ : e ∈ edges) : 0 < (d e : ℝ) :=
    Nat.cast_pos.mpr (Nat.mul_pos (Nat.cast_pos.mp (hp e.1)) (Nat.cast_pos.mp (hr e.2.1)))
  have hsum (F : E → ℂ) : (∑ e ∈ edges, F e) =
      ∑ u : IdealSelectedLabels P, ∑ z : IdealSelectedLabels R, ∑ w' ∈ S, ∑ v' ∈ T, F (u,z,w',v') :=
    comparison_cell_sum _ _ S T F
  have hcut : giantComparisonNatCutoffSum P R f g S T U V Ψ x =
      ∑ e ∈ edges, C e*Ψ ((w e : ℝ)/(x*(d e : ℝ))) := by
    rw [hsum (fun e => C e*Ψ ((w e : ℝ)/(x*(d e : ℝ))))]
    simp only [giantComparisonNatCutoffSum, mul_sum]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro z _
    apply sum_congr rfl
    intro w' _
    apply sum_congr rfl
    intro v' _
    dsimp only [C, d, w, v]
    split_ifs <;> ring
  have hphase (t : ℝ) :
      giantPhysicalMellinSum edges C (fun e => (w e : ℝ)) (fun e => (d e : ℝ)) t =
        giantComparisonNatShiftSum P R
          (fun u => f u*primeExtractionMellinPhase (-t) (idealSelectedProduct u))
          (fun z => g z*primeExtractionMellinPhase (-t) (idealSelectedProduct z))
          S T (fun w' => U w'*primeExtractionMellinPhase (-t) (w' : ℝ)) V := by
    unfold giantPhysicalMellinSum
    rw [hsum (fun e => C e*primeExtractionMellinPhase t (w e : ℝ)*
      primeExtractionMellinPhase (-t) (d e : ℝ))]
    simp only [giantComparisonNatShiftSum, mul_sum]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro z _
    apply sum_congr rfl
    intro w' _
    apply sum_congr rfl
    intro v' _
    dsimp only [C, d, w, v]
    simp only [Nat.cast_mul, comparison_mellin_phase_mul (-t) (hp u) (hr z),
      map_mul, ← Complex.star_def, giantPhysicalMellinPhase_conj, neg_neg]
    split_ifs <;> ring
  have habs :
      ((∑ e ∈ edges, ‖C e‖ : ℝ) : ℂ) =
        giantComparisonNatShiftSum P R (fun u => (‖f u‖ : ℂ)) (fun z => (‖g z‖ : ℂ))
          S T (fun w' => (‖U w'‖ : ℂ)) (fun v' => (‖V v'‖ : ℂ)) := by
    rw [Complex.ofReal_sum, hsum (fun e => (‖C e‖ : ℂ))]
    simp only [giantComparisonNatShiftSum, mul_sum]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro z _
    apply sum_congr rfl
    intro w' _
    apply sum_congr rfl
    intro v' _
    dsimp only [C, d, w, v]
    split_ifs
    · simp only [norm_mul, Complex.norm_conj, Complex.conj_ofReal, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (idealSelectedMass_nonneg P hVP u),
        abs_of_nonneg (idealSelectedMass_nonneg R hVR z), Complex.ofReal_mul]
      ring
    · simp
  have hmass := giantComparisonNatShiftSum_norm_le_sqrt P R hVP hVR
    (fun u => (‖f u‖ : ℂ)) (fun z => (‖g z‖ : ℂ))
    (fun u => by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hf u)
    (fun z => by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hg z)
    S T (fun w' => (‖U w'‖ : ℂ)) (fun v' => (‖V v'‖ : ℂ))
  rw [← habs] at hmass
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (sum_nonneg fun _ _ => norm_nonneg _)] at hmass
  have hnorm := giantPhysicalMellin_cutoff_norm_le edges C (fun e => (w e : ℝ))
    (fun e => (d e : ℝ)) Ψ ha hsupp hΨ hx hW hB n hw hd
    (fun t ht => by rw [hphase]; exact hbound t ht)
  rw [hcut]
  refine hnorm.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hmass ?_))
  apply div_nonneg
  · exact integral_nonneg fun _ => by positivity
  · positivity

end
end ArtinMatthews
