module

public import ArtinMatthews.IdealSelectedFibers
public import ArtinMatthews.IdealGroupedSelectedPairing
public import ArtinMatthews.IdealGroupedMinorBranch
public import ArtinMatthews.IdealMinorSourceBudget
public import ArtinMatthews.IdealMinorSourceGeometry
public import ArtinMatthews.MarkedMinorArcDiophantine


set_option backward.privateInPublic true
@[expose] public section

/-! The actual free-tuple product multiplier from the comparison branch.
The factorial product-atom bound controls its original harmonic measure. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantComparisonMultiplier {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]
    (P : I → Finset ℕ) (R : K → Finset ℕ)
    (f : IdealSelectedLabels P → ℂ) (g : IdealSelectedLabels R → ℂ) (α : ℝ) : ℂ :=
  ∑ x, (idealSelectedMass P x : ℂ) * f x *
    ∑ y, (idealSelectedMass R y : ℂ) * g y *
      idealProductPhase 0 α (idealSelectedProduct x) (idealSelectedProduct y)

private theorem comparison_weighted_sum_norm_le_one {I : Type*} [Fintype I]
    (μ : I → ℝ) (hμ : ∀ i, 0 ≤ μ i) (hs : ∑ i, μ i = 1)
    (f : I → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) : ‖∑ i, (μ i : ℂ) * f i‖ ≤ 1 := by
  calc
    _ ≤ ∑ i, ‖(μ i : ℂ) * f i‖ := norm_sum_le _ _
    _ ≤ ∑ i, μ i := by
      apply sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ i)]
      exact mul_le_of_le_one_right (hμ i) (hf i)
    _ = 1 := hs

private theorem comparison_phase_norm (α : ℝ) (n m : ℕ) :
    ‖idealProductPhase 0 α n m‖ = 1 := by
  simp only [idealProductPhase, Complex.ofReal_zero, mul_zero, Complex.cpow_zero,
    one_mul, Circle.norm_coe]

theorem giantComparisonMultiplier_norm_le_one {I K : Type*}
    [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]
    (P : I → Finset ℕ) (R : K → Finset ℕ)
    (hP : ∀ i, 0 < bandReciprocalMass (P i)) (hR : ∀ j, 0 < bandReciprocalMass (R j))
    (f : IdealSelectedLabels P → ℂ) (g : IdealSelectedLabels R → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1) (α : ℝ) :
    ‖giantComparisonMultiplier P R f g α‖ ≤ 1 := by
  let phase (x : IdealSelectedLabels P) (y : IdealSelectedLabels R) :=
    idealProductPhase 0 α (idealSelectedProduct x) (idealSelectedProduct y)
  let T (x : IdealSelectedLabels P) := ∑ y, (idealSelectedMass R y : ℂ) * (g y * phase x y)
  have hT (x : IdealSelectedLabels P) : ‖T x‖ ≤ 1 := by
    apply comparison_weighted_sum_norm_le_one (idealSelectedMass R) (idealSelectedMass_nonneg R hR)
      (idealSelectedMass_sum R hR)
    intro y
    change ‖g y * idealProductPhase 0 α (idealSelectedProduct x) (idealSelectedProduct y)‖ ≤ 1
    rw [norm_mul, comparison_phase_norm, mul_one]
    exact hg y
  have h := comparison_weighted_sum_norm_le_one (idealSelectedMass P) (idealSelectedMass_nonneg P hP)
    (idealSelectedMass_sum P hP) (fun x => f x * T x) (fun x => by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hT x) |>.trans (hf x))
  have hsum (x : IdealSelectedLabels P) :
      T x = ∑ y, (idealSelectedMass R y : ℂ) * g y *
        idealProductPhase 0 α (idealSelectedProduct x) (idealSelectedProduct y) := by
    simp only [T, phase, mul_assoc]
  have he : giantComparisonMultiplier P R f g α =
      ∑ x, (idealSelectedMass P x : ℂ) * (f x * T x) := by
    unfold giantComparisonMultiplier
    apply sum_congr rfl
    intro x _
    rw [← hsum x, mul_assoc]
  rw [he]
  exact h

private theorem comparison_sum_reindex {A B A' B' : Type*}
    [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    (e : A ≃ A') (e' : B ≃ B') (F : A → B → ℂ) :
    (∑ a, ∑ b, F a b) = ∑ a', ∑ b', F (e.symm a') (e'.symm b') := by
  rw [← e.symm.sum_comp (fun a => ∑ b, F a b)]
  apply sum_congr rfl
  intro a _
  exact (e'.symm.sum_comp (F (e.symm a))).symm

theorem giantComparisonMultiplier_selected_eq {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k : ℕ} (A B : Finset (G × Fin k))
    (f : IdealSelectedLabels (idealResidualBands P A) → ℂ)
    (g : IdealSelectedLabels (idealResidualBands P B) → ℂ) (α : ℝ) :
    giantComparisonMultiplier (idealResidualBands P A) (idealResidualBands P B) f g α =
      giantComparisonMultiplier
        (fun z : Σ i, Fin (idealResidualFreeSlots A i).card => P z.1)
        (fun z : Σ i, Fin (idealResidualFreeSlots B i).card => P z.1)
        (f ∘ (idealSelectedSigmaFinEquiv P A).symm)
        (g ∘ (idealSelectedSigmaFinEquiv P B).symm) α := by
  let e := idealSelectedSigmaFinEquiv P A
  let e' := idealSelectedSigmaFinEquiv P B
  let H (x : IdealSelectedLabels (idealResidualBands P A))
      (y : IdealSelectedLabels (idealResidualBands P B)) :=
    (idealSelectedMass (idealResidualBands P A) x : ℂ) * f x *
      ((idealSelectedMass (idealResidualBands P B) y : ℂ) * g y *
        idealProductPhase 0 α (idealSelectedProduct x) (idealSelectedProduct y))
  simp only [giantComparisonMultiplier, mul_sum]
  calc
    _ = ∑ x, ∑ y, H (e.symm x) (e'.symm y) := comparison_sum_reindex e e' H
    _ = _ := by
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro y _
      have hmA := (idealSelectedSigmaFin_mass P A (e.symm x)).trans
        (congrArg (idealSelectedMass _) (e.apply_symm_apply x))
      have hmB := (idealSelectedSigmaFin_mass P B (e'.symm y)).trans
        (congrArg (idealSelectedMass _) (e'.apply_symm_apply y))
      have hpA := (idealSelectedSigmaFin_product P A (e.symm x)).trans
        (congrArg idealSelectedProduct (e.apply_symm_apply x))
      have hpB := (idealSelectedSigmaFin_product P B (e'.symm y)).trans
        (congrArg idealSelectedProduct (e'.apply_symm_apply y))
      dsimp only [H, Function.comp_apply]
      rw [hmA, hmB, hpA, hpB]

private theorem comparison_energy_le_one {I : Type*} [Fintype I] [DecidableEq I]
    (P : I → Finset ℕ) (hP : ∀ i, 0 < bandReciprocalMass (P i))
    (f : IdealSelectedLabels P → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    idealFrameEnergy (idealSelectedMass P) f ≤ 1 := by
  unfold idealFrameEnergy
  calc
    _ ≤ ∑ x, idealSelectedMass P x := by
      apply sum_le_sum
      intro x _
      exact mul_le_of_le_one_right (idealSelectedMass_nonneg P hP x) (pow_le_one₀ (norm_nonneg _) (hf x))
    _ = 1 := idealSelectedMass_sum P hP

theorem giantComparisonMultiplier_sq_le {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (hP : ∀ i p, p ∈ P i → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hV : ∀ i, 0 < bandReciprocalMass (P i)) {k : ℕ} (A B : Finset (G × Fin k))
    (U V M N : ℕ) (hU : 0 < U) (hV' : 0 < V)
    (f : IdealSelectedLabels (idealResidualBands P A) → ℂ)
    (g : IdealSelectedLabels (idealResidualBands P B) → ℂ)
    (hf : ∀ a, ‖f a‖ ≤ 1) (hg : ∀ b, ‖g b‖ ≤ 1)
    (hfs : ∀ a, idealSelectedProduct a ∉ Ico U (U+M) → f a = 0)
    (hgs : ∀ b, idealSelectedProduct b ∉ Ico V (V+N) → g b = 0)
    (α : ℝ) (r : ℤ) (rden : ℕ) (hrden : 0 < rden) (hcop : IsCoprime r (rden : ℤ))
    (hrapp : |α-(r : ℝ)/rden| ≤ 1/(rden : ℝ)^2) :
    ‖giantComparisonMultiplier (idealResidualBands P A) (idealResidualBands P B) f g α‖^2 ≤
      markedMinorGramBudget M N rden *
        (idealGroupedAtomBudget P (fun i => (idealResidualFreeSlots A i).card)/(U : ℝ)) *
        (idealGroupedAtomBudget P (fun i => (idealResidualFreeSlots B i).card)/(V : ℝ)) := by
  let ka i := (idealResidualFreeSlots A i).card
  let kb i := (idealResidualFreeSlots B i).card
  let f' := f ∘ (idealSelectedSigmaFinEquiv P A).symm
  let g' := g ∘ (idealSelectedSigmaFinEquiv P B).symm
  have hf' (x : IdealSelectedLabels (fun z : Σ i, Fin (ka i) => P z.1))
      (hx : idealSelectedProduct x ∉ Ico U (U+M)) : f' x = 0 := by
    apply hfs
    simpa only [idealSelectedSigmaFin_product, Equiv.apply_symm_apply] using hx
  have hg' (y : IdealSelectedLabels (fun z : Σ i, Fin (kb i) => P z.1))
      (hy : idealSelectedProduct y ∉ Ico V (V+N)) : g' y = 0 := by
    apply hgs
    simpa only [idealSelectedSigmaFin_product, Equiv.apply_symm_apply] using hy
  have hfv := comparison_energy_le_one (fun z : Σ i, Fin (ka i) => P z.1)
    (fun z => hV z.1) f' (fun z => hf _)
  have hgv := comparison_energy_le_one (fun z : Σ i, Fin (kb i) => P z.1)
    (fun z => hV z.1) g' (fun z => hg _)
  have hraw := idealSelectedGroupedPhaseBilinear_sq_le P ka P kb hP hP hdis hdis hV hV
    U V M N hU hV' f' g' hf' hg' 0 α r rden hrden hcop hrapp
  let C := markedMinorGramBudget M N rden
  let CA := idealGroupedAtomBudget P ka / (U : ℝ)
  let CB := idealGroupedAtomBudget P kb / (V : ℝ)
  have hC : 0 ≤ C := markedMinorGramBudget_nonneg M N rden hrden
  have hCA : 0 ≤ CA := div_nonneg (idealGroupedAtomBudget_nonneg P ka hV) (Nat.cast_nonneg _)
  have hCB : 0 ≤ CB := div_nonneg (idealGroupedAtomBudget_nonneg P kb hV) (Nat.cast_nonneg _)
  have hEg := idealFrameEnergy_nonneg _
    (idealSelectedMass_nonneg (fun z : Σ i, Fin (kb i) => P z.1) (fun z => hV z.1)) g'
  rw [giantComparisonMultiplier_selected_eq P A B f g α]
  refine hraw.trans ?_
  exact mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hCA hfv) hC)
    (mul_le_of_le_one_right hCB hgv) (mul_nonneg hCB hEg) (mul_nonneg hC hCA)

def giantComparisonArcExponent (m : ℕ) (C₀ v₀ d E : ℝ) : ℝ :=
  idealMinorCutoffExponent E (idealGroupedBudgetExponent m C₀ v₀) d

theorem giantComparisonMultiplier_minor_eventually (m : ℕ) (C₀ v₀ c d E : ℝ)
    (hC₀ : 0 ≤ C₀) (hv₀ : 0 < v₀) (hc : 0 < c) (hd : 0 ≤ d) (hE : 0 ≤ E) :
    ∀ᶠ L : ℝ in atTop, ∀ {G : Type} [Fintype G] [DecidableEq G],
      ∀ (P : G → Finset ℕ), (∀ i p, p ∈ P i → p.Prime) →
      Pairwise (fun i j => Disjoint (P i) (P j)) →
      (∀ i, v₀ ≤ bandReciprocalMass (P i)) →
      (Fintype.card G : ℝ) ≤ C₀ * Real.log L →
      ∀ {k : ℕ} (A B : Finset (G × Fin k)),
      (∀ i, (idealResidualFreeSlots A i).card ≤ m) →
      (∀ i, (idealResidualFreeSlots B i).card ≤ m) →
      ∀ U V : ℕ, 0 < U → 0 < V →
      Real.exp (L^c)/4 ≤ (U : ℝ) → Real.exp (L^c)/4 ≤ (V : ℝ) →
      Real.log ((4*U : ℕ) : ℝ) ≤ L^(d+2) → Real.log ((4*V : ℕ) : ℝ) ≤ L^(d+2) →
      ∀ (f : IdealSelectedLabels (idealResidualBands P A) → ℂ)
        (g : IdealSelectedLabels (idealResidualBands P B) → ℂ),
      (∀ a, ‖f a‖ ≤ 1) → (∀ b, ‖g b‖ ≤ 1) →
      (∀ a, idealSelectedProduct a ∉ Ico U (U+4*U) → f a = 0) →
      (∀ b, idealSelectedProduct b ∉ Ico V (V+4*V) → g b = 0) →
      ∀ α : ℝ, ¬MarkedInRationalArc α (L^(giantComparisonArcExponent m C₀ v₀ d E))
        (L^(giantComparisonArcExponent m C₀ v₀ d E)/((U : ℝ)*(V : ℝ))) →
      ‖giantComparisonMultiplier (idealResidualBands P A) (idealResidualBands P B) f g α‖ ≤ L^(-E) := by
  let κ := idealGroupedBudgetExponent m C₀ v₀
  let a := giantComparisonArcExponent m C₀ v₀ d E
  have hκ : 0 ≤ κ := by
    unfold κ idealGroupedBudgetExponent
    exact mul_nonneg hC₀ (add_nonneg
      (Real.log_nonneg (by exact_mod_cast Nat.factorial_pos m))
      (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (le_max_left _ _))))
  have ha : 0 ≤ a := by unfold a giantComparisonArcExponent idealMinorCutoffExponent; linarith
  have hfast := (rpow_mul_exp_neg_rpow_tendsto a hc (by norm_num : (0 : ℝ) < 1)).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hexp16 := (Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop hc)).eventually_ge_atTop 16
  filter_upwards [idealMinorGramBudget_source c d E κ hc hd, idealSource_gram_log_bound d hd,
    hfast, hexp16, eventually_ge_atTop (1 : ℝ)] with L hgram hlog hfast h16 hL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  intro G _ _ P hP hdis hV hcard k A B hA hB U V hU hV' hUlo hVlo hUlog hVlog f g hf hg hfs hgs α hminor
  let Q := L^a
  have hQp : 0 < Q := Real.rpow_pos_of_pos hLp _
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hL ha
  have hUV : Q ≤ (U : ℝ)*(V : ℝ) := by
    have hx : Q ≤ Real.exp (L^c) := by
      have hd : Q / Real.exp (L^c) ≤ 1 := by
        simpa only [div_eq_mul_inv, neg_one_mul, Real.exp_neg, Q] using hfast.le
      simpa only [one_mul] using (div_le_iff₀ (Real.exp_pos (L^c))).mp hd
    have hy := mul_le_mul hUlo hVlo (by positivity : 0 ≤ Real.exp (L^c)/4) (Nat.cast_nonneg U)
    change 16 ≤ Real.exp (L^c) at h16
    have hge : 0 ≤ Real.exp (L^c) * (Real.exp (L^c)-16) :=
      mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr h16)
    exact hx.trans (by nlinarith only [hy, hge])
  obtain ⟨r,hrlo,hrhi,happrox⟩ := marked_minor_rational_approximation hQp hUV hminor
  have hcop : IsCoprime r.num (r.den : ℤ) := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    simpa only [Int.gcd_def, Int.natAbs_natCast] using r.reduced.gcd_eq_one
  have hrapp : |α-(r.num : ℝ)/r.den| ≤ 1/(r.den : ℝ)^2 := by
    simpa only [Rat.cast_def] using happrox
  let ka i := (idealResidualFreeSlots A i).card
  let kb i := (idealResidualFreeSlots B i).card
  have hVpos i := hv₀.trans_le (hV i)
  have hraw := giantComparisonMultiplier_sq_le P hP hdis hVpos A B U V (4*U) (4*V)
    hU hV' f g hf hg hfs hgs α r.num r.den r.pos hcop hrapp
  have hU4 : (U : ℝ) ≤ ((4*U : ℕ) : ℝ) := by push_cast; linarith [show (0 : ℝ) ≤ U from Nat.cast_nonneg U]
  have hV4 : (V : ℝ) ≤ ((4*V : ℕ) : ℝ) := by push_cast; linarith [show (0 : ℝ) ≤ V from Nat.cast_nonneg V]
  have hr4 : (r.den : ℝ) ≤ ((4*U : ℕ) : ℝ)*((4*V : ℕ) : ℝ)/Q :=
    hrhi.trans (div_le_div_of_nonneg_right (by gcongr) hQp.le)
  have hprod0 : 0 ≤ ((4*U : ℕ) : ℝ)*((4*V : ℕ) : ℝ) := by positivity
  have hlogr := hlog (4*U) (4*V) r.den (by omega) (by omega) r.pos hUlog hVlog
    (hr4.trans ((div_le_self hprod0 hQ1).trans (by nlinarith only [hprod0])))
  have hG := hgram (4*U) (4*V) r.den (by omega) (by omega) r.pos
    (hUlo.trans hU4) (hVlo.trans hV4) (show Q/2 ≤ (r.den : ℝ) by linarith)
    hr4 hlogr
  have hbA := idealGroupedAtomBudget_power P ka hv₀ hL hV hA hcard
  have hbB := idealGroupedAtomBudget_power P kb hv₀ hL hV hB hcard
  have hA0 := idealGroupedAtomBudget_nonneg P ka hVpos
  have hB0 := idealGroupedAtomBudget_nonneg P kb hVpos
  have hG0 := markedMinorGramBudget_nonneg (4*U) (4*V) r.den r.pos
  have hcoef : idealGroupedAtomBudget P ka * idealGroupedAtomBudget P kb ≤ L^(2*κ) := by
    calc
      _ ≤ L^κ * L^κ := mul_le_mul hbA hbB hB0 (Real.rpow_nonneg hLp.le _)
      _ = _ := by rw [← Real.rpow_add hLp]; congr 1; ring
  apply (sq_le_sq₀ (norm_nonneg _) (Real.rpow_nonneg hLp.le _)).mp
  have hpow : (L^(-E))^2 = L^(-2*E) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLp.le]
    congr 1
    norm_num
    ring
  rw [hpow]
  calc
    _ ≤ markedMinorGramBudget (4*U) (4*V) r.den *
        (idealGroupedAtomBudget P ka / (U : ℝ)) * (idealGroupedAtomBudget P kb / (V : ℝ)) := hraw
    _ = 16*(idealGroupedAtomBudget P ka * idealGroupedAtomBudget P kb) *
        (markedMinorGramBudget (4*U) (4*V) r.den / (((4*U : ℕ) : ℝ)*((4*V : ℕ) : ℝ))) := by
      push_cast
      have hUr : (U : ℝ) ≠ 0 := by exact_mod_cast hU.ne'
      have hVr : (V : ℝ) ≠ 0 := by exact_mod_cast hV'.ne'
      field_simp
      <;> ring
    _ ≤ 64*L^(2*κ)*(markedMinorGramBudget (4*U) (4*V) r.den /
          (((4*U : ℕ) : ℝ)*((4*V : ℕ) : ℝ))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc
        _ ≤ 16*L^(2*κ) := mul_le_mul_of_nonneg_left hcoef (by norm_num)
        _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hLp.le _)
    _ ≤ L^(-2*E) := hG

end
end ArtinMatthews
