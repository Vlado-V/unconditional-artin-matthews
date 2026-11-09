module

public import ArtinMatthews.SourceComparisonProductEnergy
public import ArtinMatthews.SourceComparisonConstantDyadEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! High-time saving after summing all occupied dyads in both product sums. -/

namespace ArtinMatthews

open Finset Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

theorem sourceComparisonProductBranches_high_energy
    (ψ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support ψ ⊆ Set.Icc a b) (hψ : ContDiff ℝ ∞ ψ)
    (ε C D Q E K A : ℝ) (hε : 0 < ε) (hεq : ε < 1/4)
    (hD : 0 ≤ D) (hQ : 0 ≤ Q) (hE : 0 ≤ E) (hA : 0 ≤ A) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (Y H σ : ℝ), Real.exp X ≤ Y → Y ≤ Real.exp ((1+ε/4)*X) →
        Real.exp (X^(38/100:ℝ)) ≤ H → H ≤ Real.exp (X/2) → |σ| ≤ X^C →
        ∀ (S : Finset ℕ) (β : ℕ → ℂ),
          (∀ p ∈ S, p.Prime ∧ Real.exp (X^(28/100:ℝ)) ≤ (p:ℝ) ∧
            (p:ℝ) ≤ Real.exp (X^(36/100:ℝ))) →
          (∀ n ∈ Ioc 0 ⌊b*Y⌋₊, ‖β n‖ ≤ X^D) →
          ∀ {ι : Type*} (J : Finset ι) (divisor : ι → ℕ) (coeff : ι → ℂ),
            (∀ i ∈ J, 0 < divisor i ∧ (divisor i:ℝ) ≤ Real.exp (K*X^(47/100:ℝ))) →
            (∑ i ∈ J, ‖coeff i‖/(divisor i:ℝ)) ≤ X^E →
            (∀ N : ℕ, (∑ n ∈ Ioc 0 N,
              ‖β n-markedMajorDivisorPolynomial J divisor coeff n‖^2) ≤
                (N:ℝ)*X^(-(A+13+2*Q))) →
            ∀ (q : ℕ) [NeZero q] (h : ZMod q), (q:ℝ) ≤ X^Q →
              let W := sourceComparisonHighTimes (X*Y/H) (X^B)
              let R := Ioc 0 ⌊b*Y⌋₊
              (∫ t in W, ‖sourceComparisonProductMellin h S (giantPrimeWindow (Real.exp X) ε)
                R β ψ Y (t+σ)‖^2) ≤ X^(-A) ∧
              (∫ t in W, ‖sourceComparisonProductMellin h S {1} R β ψ Y (t+σ)‖^2) ≤ X^(-A) := by
  let M := A+7
  let G₀ := (1+(Real.log 2+3)/Real.log 2)
  have hM : 0 ≤ M := by dsimp [M]; linarith
  obtain ⟨B₁,hB₁,hp⟩ := sourceComparisonPositiveDyad_high_energy ψ ha hsupp hψ ε C D Q M hε hεq hD hQ hM
  obtain ⟨B₂,hB₂,hc⟩ := sourceComparisonConstantDyad_high_energy ψ ha hsupp hψ ε C D Q E K M
    hε hεq hD hQ hE hM
  let B := max B₁ B₂
  refine ⟨B,hB₁.trans_le (le_max_left _ _),?_⟩
  filter_upwards [hp,hc,eventually_ge_atTop (max 1 (G₀^6)),
    Real.tendsto_exp_atTop.eventually (eventually_ge_atTop b)] with X hp hc hX hxb
  have hX1 : 1 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := zero_lt_one.trans_le hX1
  have hGX : G₀^6 ≤ X := (le_max_right _ _).trans hX
  intro Y H σ hY hYcap hH hHcap hσ S β hS hβ ι J divisor coeff hd hm he q _ h hq
  let W := sourceComparisonHighTimes (X*Y/H) (X^B)
  let R := Ioc 0 ⌊b*Y⌋₊
  let G := giantPrimeWindow (Real.exp X) ε
  have hY0 : 0 < Y := (Real.exp_pos _).trans_le hY
  have hS0 (n : ℕ) (hn : n ∈ S) : 0 < n := (hS n hn).1.pos
  have hR0 (n : ℕ) (hn : n ∈ R) : 0 < n := (mem_Ioc.mp hn).1
  have hG0 (n : ℕ) (hn : n ∈ G) : 0 < n := ((mem_giantPrimeWindow (Real.exp_pos X).le).mp hn).1.pos
  have hS3 (n : ℕ) (hn : n ∈ S) : (n:ℝ) ≤ Real.exp (3*X) := by
    apply (hS n hn).2.2.trans
    apply Real.exp_le_exp.mpr
    have hx := Real.rpow_le_rpow_of_exponent_le hX1 (show (36/100:ℝ) ≤ 1 by norm_num)
    rw [Real.rpow_one] at hx
    linarith
  have hG3 (n : ℕ) (hn : n ∈ G) : (n:ℝ) ≤ Real.exp (3*X) := by
    have hh := ((mem_giantPrimeWindow (Real.exp_pos X).le).mp hn).2.2
    rw [← Real.exp_mul] at hh
    exact hh.trans (Real.exp_le_exp.mpr (by nlinarith))
  have hR3 (n : ℕ) (hn : n ∈ R) : (n:ℝ) ≤ Real.exp (3*X) := by
    have hbY : 0 ≤ b*Y := by
      have h : 0 < ⌊b*Y⌋₊ := (hR0 n hn).trans_le (mem_Ioc.mp hn).2
      exact zero_le_one.trans (Nat.floor_pos.mp h)
    calc
      _ ≤ (⌊b*Y⌋₊:ℝ) := by exact_mod_cast (mem_Ioc.mp hn).2
      _ ≤ b*Y := Nat.floor_le hbY
      _ ≤ Real.exp X*Real.exp ((1+ε/4)*X) :=
        mul_le_mul hxb hYcap hY0.le (Real.exp_pos _).le
      _ ≤ _ := by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
  have hB₁ : X^B₁ ≤ X^B := Real.rpow_le_rpow_of_exponent_le hX1 (le_max_left _ _)
  have hB₂ : X^B₂ ≤ X^B := Real.rpow_le_rpow_of_exponent_le hX1 (le_max_right _ _)
  have hcost (J : Finset (ℕ × ℕ × ℕ)) (hj : (J.card:ℝ) ≤ G₀^3*X^3) :
      (J.card:ℝ)^2*X^(-M) ≤ X^(-A) := by
    calc
      _ ≤ (G₀^3*X^3)^2*X^(-M) := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hj 2) (by positivity)
      _ = G₀^6*X^(-A-1) := by
        have hs : (X^3)^2 = X^(6:ℕ) := by ring
        rw [mul_pow, hs, ← Real.rpow_natCast X (6:ℕ)]
        norm_num only [Nat.cast_ofNat]
        have ht : X^(6:ℝ)*X^(-M)=X^(-A-1) := by
          rw [← Real.rpow_add hX0]
          congr 1
          dsimp [M]
          ring
        rw [mul_assoc, ht]
        ring
      _ ≤ X*X^(-A-1) := mul_le_mul_of_nonneg_right hGX (by positivity)
      _ = _ := by
        conv_lhs => lhs; rw [← Real.rpow_one X]
        rw [← Real.rpow_add hX0]
        congr 1
        ring
  have hp' := hp Y H σ hY hYcap hH hHcap hσ S β hS hβ q h hq
  have he' (N : ℕ) :
      (∑ n ∈ Ioc 0 N, ‖β n-markedMajorDivisorPolynomial J divisor coeff n‖^2) ≤
        (N:ℝ)*X^(-(M+3+2*Q+2)-1) := by
    have hh : -(M+3+2*Q+2)-1 = -(A+13+2*Q) := by dsimp [M]; ring
    rw [hh]
    exact he N
  have hc' := hc Y H σ hY hYcap hH hHcap hσ S β hS hβ J divisor coeff hd hm he' q h hq
  have hjoin (L : Finset ℕ) (hL : ∀ n ∈ L, 0 < n)
      (hL3 : ∀ n ∈ L, (n:ℝ) ≤ Real.exp (3*X)) (B₀ : ℝ) (hB₀ : X^B₀ ≤ X^B)
      (hE : ∀ j ∈ sourceComparisonOccupiedDyads S L R a b Y,
        (∫ t in sourceComparisonHighTimes (X*Y/H) (X^B₀), ‖sourceComparisonCutTriple
          (sourceComparisonProductBox S L R j) (sourceComparisonProductCoefficient h β)
          ψ Y Y (t+σ)‖^2) ≤ X^(-M)) :
      (∫ t in W, ‖sourceComparisonProductMellin h S L R β ψ Y (t+σ)‖^2) ≤ X^(-A) := by
    have hh := sourceComparisonProductMellin_energy_from_boxes h S L R β ψ a b Y (X*Y/H) (X^B) σ
      hY0 hsupp hS0 hL hR0 (X^(-M)) (fun j hj =>
        (sourceComparison_high_energy_mono_threshold _ ((sourceComparisonCutTriple_continuous _ _ _ _ _).comp
          (continuous_id.add continuous_const)) _ _ _ hB₀).trans (hE j hj))
    exact hh.trans (hcost _ (sourceComparisonOccupiedDyads_log_card X hX1 S L R a b Y hS3 hL3 hR3))
  exact ⟨hjoin G hG0 hG3 B₁ hB₁ hp',
    hjoin {1} (fun n hn => by rw [mem_singleton.mp hn]; norm_num)
      (fun n hn => by rw [mem_singleton.mp hn]; simpa only [Nat.cast_one] using Real.one_le_exp (show 0 ≤ 3*X by positivity))
      B₂ hB₂ hc'⟩

end
end ArtinMatthews
