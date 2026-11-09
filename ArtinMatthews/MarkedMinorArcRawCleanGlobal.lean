module

public import ArtinMatthews.MarkedMinorArcRawShiftBlocks
public import ArtinMatthews.MarkedMinorArcShiftedPartition


set_option backward.privateInPublic true
@[expose] public section

/-! Full actual raw clean operator assembly. Literal root-line/cell classes
are summed without cardinality loss, then the cutoff-derived finite shifts
are absorbed using one fixed logarithmic margin. -/
namespace ArtinMatthews
open Matrix Filter
open scoped BigOperators Matrix.Norms.L2Operator

set_option maxHeartbeats 1500000 in
/-- Every actual full-fiber cell shift satisfies the true clean norm bound;
all its infinitely indexed possible line/cell keys are handled by their
finite physical image, without a class-count factor. -/
theorem marked_minor_actual_raw_shift_opNorm {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ t, ‖η t‖ ≤ 1)
    {G H c L : ℝ} (hG : 0 < G) (hH : 1 ≤ H) (hc : 0 < c) (hL : 0 ≤ L) (N : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (q r d₀ Y ρ : ℝ)
      (w : Z → ℤ × ℤ) (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
      (bg : MarkedRawBackground (markedRawActualPrimeBand e x) pads B) (shift : ℤ),
      0 ≤ q → q ≤ 1 → 0 < d₀ → 0 ≤ ρ → ρ ≤ 1 →
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (H*(Real.log x)^(1/5:ℝ)) →
      (∀ z, markedMinorIntegerDet z.1 (w z)=1) →
      (∀ z ∈ Z, c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ L) →
      (∀ s, ‖χ s‖ ≤ 1) → |shift| ≤ (N : ℤ) →
      ‖markedRawCleanShiftCountingMatrix (markedRawActualPrimeAtom e q x) hZ ψ η r d₀ Y
        ((Real.log x)^(G+4)) ρ (markedRawFirstGoodCutoff r d₀ Y w χ) bg shift‖ ≤
        (Real.log x)^(-G) := by
  classical
  filter_upwards [marked_minor_actual_raw_shift_class_opNorm e he hinj ψ η hη hηnorm hG hH hc hL N,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hlog
  intro pads B Z hZ q r d₀ Y ρ w χ bg shift hq₀ hq₁ hd₀ hρ₀ hρ₁ hYlo hYhi hw hτ hχ hshift
  apply markedMinorShiftedPartition_norm_le _
    (fun u => markedRawPositionKey hZ r d₀ Y (markedRawCopiedProduct bg.1) u.1)
    (markedRawShiftKey shift) (markedRawShiftKey_injective _ shift)
    (markedRawCleanShiftCountingMatrix_off_key _ hZ ψ η r d₀ Y _ ρ _ bg shift)
    (Real.rpow_nonneg (by linarith : (0:ℝ)≤Real.log x) _)
  intro key
  exact hx pads B Z hZ q r d₀ Y ρ w χ bg shift key
    hq₀ hq₁ hd₀ hρ₀ hρ₁ hYlo hYhi hw hτ hχ hshift

/-- Square-root measure conjugation preserves exact finite kernel sums. -/
theorem markedWeightedCountingMatrix_sum {ι T : Type*} [Fintype ι]
    (mass : ι → ℝ) (S : Finset T) (K : T → Matrix ι ι ℂ) :
    markedWeightedCountingMatrix mass (∑ t ∈ S, K t)=
      ∑ t ∈ S, markedWeightedCountingMatrix mass (K t) := by
  ext i j
  simp only [markedWeightedCountingMatrix,Matrix.sum_apply,Finset.mul_sum,Finset.sum_mul]

set_option maxHeartbeats 1500000 in
/-- Full literal actual raw clean norm, including every copied background,
all indexed pending particles, physical distinctness and the actual
first-good projection. The major cutoff exponent G+5 depends on G alone. -/
theorem marked_minor_actual_raw_clean_opNorm {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ t, ‖η t‖ ≤ 1)
    {G H c L K : ℝ} (hG : 0 < G) (hH : 1 ≤ H) (hc : 0 < c) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (q r d₀ Y ρ : ℝ)
      (w : Z → ℤ × ℤ) (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
      (bg : MarkedRawBackground (markedRawActualPrimeBand e x) pads B),
      0 ≤ q → q ≤ 1 → 0 < d₀ → 0 ≤ ρ → ρ ≤ 1 →
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (H*(Real.log x)^(1/5:ℝ)) →
      (∀ z, markedMinorIntegerDet z.1 (w z)=1) →
      (∀ z ∈ Z, c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ L) →
      (∀ s, ‖χ s‖ ≤ 1) →
      ‖markedWeightedCountingMatrix
        (fun u : MarkedRawCleanFiber (markedRawActualPrimeBand e x) Z =>
          markedRawLastMass (markedRawActualPrimeAtom e q x) u.2)
        (markedRawCleanKernel hZ ψ η d₀ Y ((Real.log x)^(G+5)) ρ
          (markedRawFirstGoodCutoff r d₀ Y w χ) bg)‖ ≤ (Real.log x)^(-G) := by
  classical
  let N : ℕ := ⌈2*K/c^2+1⌉₊
  let S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hshift := marked_minor_actual_raw_shift_opNorm e he hinj ψ η hη hηnorm
    (show 0<G+1 by linarith) hH hc hL N
  simp only [show (G+1)+4=G+5 by ring] at hshift
  filter_upwards [hshift,markedRawActualPrimeBand_disjoint_eventually e hinj,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (S.card : ℝ)))] with x hx hdis hlog
  intro pads B Z hZ q r d₀ Y ρ w χ bg hq₀ hq₁ hd₀ hρ₀ hρ₁ hYlo hYhi hw hτ hχ
  have hY : 0 < Y := (Real.exp_pos _).trans_le hYlo
  have hlogp : 0 < Real.log x := (by norm_num : (0:ℝ)<1).trans_le ((le_max_left _ _).trans hlog)
  have hcount : (S.card : ℝ) ≤ Real.log x := (le_max_right _ _).trans hlog
  rw [markedRawCleanKernel_eq_sum_shifts hdis hZ ψ η hd₀ hY hc hK hψ r _ ρ
    (fun z hz => (hτ z hz).1),markedWeightedCountingMatrix_sum]
  change ‖∑ shift ∈ S, markedRawCleanShiftCountingMatrix (markedRawActualPrimeAtom e q x)
    hZ ψ η r d₀ Y ((Real.log x)^(G+5)) ρ (markedRawFirstGoodCutoff r d₀ Y w χ) bg shift‖ ≤ _
  have hr : (Real.log x)^(-(G+1))=(Real.log x)^(-G)*(Real.log x)⁻¹ := by
    rw [← Real.rpow_neg_one,← Real.rpow_add hlogp]
    congr 1
    ring
  calc
    _ ≤ ∑ shift ∈ S, ‖markedRawCleanShiftCountingMatrix (markedRawActualPrimeAtom e q x)
        hZ ψ η r d₀ Y ((Real.log x)^(G+5)) ρ (markedRawFirstGoodCutoff r d₀ Y w χ) bg shift‖ := norm_sum_le _ _
    _ ≤ ∑ _shift ∈ S, (Real.log x)^(-(G+1)) := by
      apply Finset.sum_le_sum
      intro shift hs
      have hsb : |shift| ≤ (N : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hs)
      exact hx pads B Z hZ q r d₀ Y ρ w χ bg shift hq₀ hq₁ hd₀ hρ₀ hρ₁ hYlo hYhi hw hτ hχ hsb
    _ = (S.card : ℝ)*(Real.log x)^(-(G+1)) := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (Real.log x)*(Real.log x)^(-(G+1)) :=
      mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg hlogp.le _)
    _ = _ := by rw [hr]; field_simp

end ArtinMatthews
