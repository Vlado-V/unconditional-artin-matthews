module

public import ArtinMatthews.ProbeBadPrimeWeights


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute convergence of the literal bad-prime series and a quantitative
remainder estimate before substituting the manuscript regions. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField Classical BigOperators Topology
noncomputable section

theorem probe_geometric_pair_hasSum {A B : ℝ} (hA0 : 0 ≤ A) (hA : A < 1)
    (hB0 : 0 ≤ B) (hB : B < 1) :
    HasSum (fun v : ℕ × ℕ => A ^ v.1 * B ^ v.2) ((1 - A)⁻¹ * (1 - B)⁻¹) := by
  have ha := hasSum_geometric_of_lt_one hA0 hA
  have hb := hasSum_geometric_of_lt_one hB0 hB
  exact ha.mul hb (ha.summable.mul_of_nonneg hb.summable
    (fun _ => pow_nonneg hA0 _) (fun _ => pow_nonneg hB0 _))

theorem probe_pair_tsum_head {f : ℕ × ℕ → ℂ} (hf : Summable f) :
    (∑' v, f v) = (∑' m : ℕ, f (0, m)) + ∑' v : ℕ × ℕ, f (v.1 + 1, v.2) := by
  have ht : Summable (fun v : ℕ × ℕ => f (v.1 + 1, v.2)) :=
    hf.comp_injective (by
      intro v w h
      apply Prod.ext
      · exact Nat.add_right_cancel (congrArg Prod.fst h)
      · simpa only using congrArg (Prod.snd : ℕ × ℕ → ℕ) h)
  rw [hf.tsum_prod, ht.tsum_prod]
  simpa only [Finset.sum_range_one] using (hf.prod.sum_add_tsum_nat_add 1).symm

variable (K : Type*) [Field K] [NumberField K]

def probeBadE (Q : ℝ) (a : ℂ) : ℝ := Q * ‖a‖
def probeBadA (Q : ℝ) (b : ℂ) : ℝ := Q ^ 3 * ‖b‖
def probeBadT (Q : ℝ) (W : ℂ) : ℝ := Real.sqrt Q * ‖W‖

def probeBadPrimePair (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (j : ℕ)
    (a b W V : ℂ) (e k : Fin 2) (n : ℕ) (v : ℕ × ℕ) : ℂ :=
  probeBadPrimeWeight K p hp χ j a b W V e (v.1 + n) k.val v.2

theorem probeBadPrimePair_norm_bound (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (a b W V : ℂ) (e k : Fin 2) (n : ℕ)
    (v : ℕ × ℕ) :
    ‖probeBadPrimePair K p hp.ne_zero χ j a b W V e k n v‖ ≤
      (probeBadE (Ideal.absNorm (Ideal.span {p})) a ^ e.val *
        probeBadT (Ideal.absNorm (Ideal.span {p})) W ^ k.val *
        probeBadA (Ideal.absNorm (Ideal.span {p})) b ^ n) *
      (probeBadA (Ideal.absNorm (Ideal.span {p})) b ^ v.1 * ‖V‖ ^ v.2) := by
  apply (probeBadPrimeWeight_norm_le K p hp χ hχ hminus j a b W V e k (v.1 + n) v.2).trans_eq
  simp only [probeBadE, probeBadA, probeBadT, pow_add]
  ring

theorem probeBadPrimePair_summable (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (a b W V : ℂ)
    (hA : probeBadA (Ideal.absNorm (Ideal.span {p})) b < 1) (hV : ‖V‖ < 1)
    (e k : Fin 2) (n : ℕ) :
    Summable (probeBadPrimePair K p hp.ne_zero χ j a b W V e k n) := by
  have hg := probe_geometric_pair_hasSum
    (by unfold probeBadA; positivity) hA (norm_nonneg V) hV
  exact Summable.of_norm_bounded (hg.mul_left
    (probeBadE (Ideal.absNorm (Ideal.span {p})) a ^ e.val *
      probeBadT (Ideal.absNorm (Ideal.span {p})) W ^ k.val *
      probeBadA (Ideal.absNorm (Ideal.span {p})) b ^ n)).summable
    (probeBadPrimePair_norm_bound K p hp χ hχ hminus j a b W V e k n)

theorem probeBadPrimePair_tsum_norm_le (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (a b W V : ℂ)
    (hA : probeBadA (Ideal.absNorm (Ideal.span {p})) b < 1) (hV : ‖V‖ < 1)
    (e k : Fin 2) (n : ℕ) :
    ‖∑' v, probeBadPrimePair K p hp.ne_zero χ j a b W V e k n v‖ ≤
      (probeBadE (Ideal.absNorm (Ideal.span {p})) a ^ e.val *
        probeBadT (Ideal.absNorm (Ideal.span {p})) W ^ k.val *
        probeBadA (Ideal.absNorm (Ideal.span {p})) b ^ n) *
      ((1 - probeBadA (Ideal.absNorm (Ideal.span {p})) b)⁻¹ * (1 - ‖V‖)⁻¹) := by
  have hg := probe_geometric_pair_hasSum
    (by unfold probeBadA; positivity) hA (norm_nonneg V) hV
  exact tsum_of_norm_bounded (hg.mul_left _) (probeBadPrimePair_norm_bound K p hp χ hχ hminus j a b W V e k n)

def probeBadPrimeLocalSeries (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (j : ℕ) (a b W V : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑ k : Fin 2, ∑' v,
    probeBadPrimePair K p hp χ j a b W V e k 0 v

def probeBadPrimeTail (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (j : ℕ) (a b W V : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑ k : Fin 2, ∑' v,
    probeBadPrimePair K p hp χ j a b W V e k 1 v

theorem probeBadPrimeLocalSeries_decompose (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j) (a b W V : ℂ)
    (hA : probeBadA (Ideal.absNorm (Ideal.span {p})) b < 1) (hV : ‖V‖ < 1) :
    probeBadPrimeLocalSeries K p hp.ne_zero χ j a b W V =
      (1 - V)⁻¹ + (∑' m : ℕ, probeBadPrimeWeight K p hp.ne_zero χ j a b W V 1 0 1 m) +
        probeBadPrimeTail K p hp.ne_zero χ j a b W V := by
  have hh (e k : Fin 2) := probe_pair_tsum_head
    (probeBadPrimePair_summable K p hp χ hχ hminus j a b W V hA hV e k 0)
  have hd (e k : Fin 2) : (∑' v, probeBadPrimePair K p hp.ne_zero χ j a b W V e k 0 v) =
      (∑' m : ℕ, probeBadPrimeWeight K p hp.ne_zero χ j a b W V e 0 k.val m) +
        ∑' v, probeBadPrimePair K p hp.ne_zero χ j a b W V e k 1 v := by
    simpa only [probeBadPrimePair, add_zero] using hh e k
  unfold probeBadPrimeLocalSeries probeBadPrimeTail
  simp only [hd, Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
    probeBadPrimeWeight_base, probeBadPrimeWeight_zero_outer K p hp χ j hj,
    probeBadPrimeWeight_first_zero K p hp χ hχ j hj, tsum_zero, zero_add]
  rw [(hasSum_geometric_of_norm_lt_one hV).tsum_eq]
  ring

theorem probeBadPrimeTail_norm_le (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (a b W V : ℂ)
    (hA : probeBadA (Ideal.absNorm (Ideal.span {p})) b < 1) (hV : ‖V‖ < 1) :
    ‖probeBadPrimeTail K p hp.ne_zero χ j a b W V‖ ≤
      (1 + probeBadE (Ideal.absNorm (Ideal.span {p})) a) *
      (1 + probeBadT (Ideal.absNorm (Ideal.span {p})) W) *
      probeBadA (Ideal.absNorm (Ideal.span {p})) b *
      ((1 - probeBadA (Ideal.absNorm (Ideal.span {p})) b)⁻¹ * (1 - ‖V‖)⁻¹) := by
  calc
    _ ≤ ∑ e : Fin 2, ∑ k : Fin 2,
        ‖∑' v, probeBadPrimePair K p hp.ne_zero χ j a b W V e k 1 v‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ e : Fin 2, ∑ k : Fin 2,
        (probeBadE (Ideal.absNorm (Ideal.span {p})) a ^ e.val *
          probeBadT (Ideal.absNorm (Ideal.span {p})) W ^ k.val *
          probeBadA (Ideal.absNorm (Ideal.span {p})) b ^ 1) *
        ((1 - probeBadA (Ideal.absNorm (Ideal.span {p})) b)⁻¹ * (1 - ‖V‖)⁻¹) :=
      Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun k _ =>
        probeBadPrimePair_tsum_norm_le K p hp χ hχ hminus j a b W V hA hV e k 1
    _ = _ := by simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]; ring

theorem probeBadPrimeFirst_norm_le (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (a b W V : ℂ) (hV : ‖V‖ < 1) :
    ‖∑' m : ℕ, probeBadPrimeWeight K p hp.ne_zero χ j a b W V 1 0 1 m‖ ≤
      probeBadE (Ideal.absNorm (Ideal.span {p})) a *
      probeBadT (Ideal.absNorm (Ideal.span {p})) W * (1 - ‖V‖)⁻¹ := by
  apply tsum_of_norm_bounded
    ((hasSum_geometric_of_lt_one (norm_nonneg V) hV).mul_left _)
  intro m
  simpa only [Fin.val_one, pow_one, pow_zero, mul_one, probeBadE, probeBadT, mul_assoc] using
    probeBadPrimeWeight_norm_le K p hp χ hχ hminus j a b W V 1 1 0 m

def probeBadPrimeCorrection (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (j : ℕ) (a b W V : ℂ) : ℂ :=
  (1 - V) * probeBadPrimeLocalSeries K p hp χ j a b W V

theorem probeBadPrimeCorrection_sub_one (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j) (a b W V : ℂ)
    (hA : probeBadA (Ideal.absNorm (Ideal.span {p})) b < 1) (hV : ‖V‖ < 1) :
    probeBadPrimeCorrection K p hp.ne_zero χ j a b W V - 1 =
      (1 - V) * ((∑' m : ℕ, probeBadPrimeWeight K p hp.ne_zero χ j a b W V 1 0 1 m) +
        probeBadPrimeTail K p hp.ne_zero χ j a b W V) := by
  have hV0 : 1 - V ≠ 0 := sub_ne_zero.mpr (ne_of_apply_ne norm (by simpa using hV.ne)).symm
  rw [probeBadPrimeCorrection,
    probeBadPrimeLocalSeries_decompose K p hp χ hχ hminus j hj a b W V hA hV,
    mul_add, mul_add, mul_inv_cancel₀ hV0]
  ring

theorem probeBadPrimeCorrection_norm_sub_one_le (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j) (a b W V : ℂ)
    (hA : probeBadA (Ideal.absNorm (Ideal.span {p})) b ≤ 1 / 2) (hV : ‖V‖ ≤ 1 / 2) :
    ‖probeBadPrimeCorrection K p hp.ne_zero χ j a b W V - 1‖ ≤
      4 * (probeBadE (Ideal.absNorm (Ideal.span {p})) a *
        probeBadT (Ideal.absNorm (Ideal.span {p})) W) +
      8 * ((1 + probeBadE (Ideal.absNorm (Ideal.span {p})) a) *
        (1 + probeBadT (Ideal.absNorm (Ideal.span {p})) W) *
        probeBadA (Ideal.absNorm (Ideal.span {p})) b) := by
  have hA0 : 0 ≤ probeBadA (Ideal.absNorm (Ideal.span {p})) b := by
    unfold probeBadA; positivity
  have hE0 : 0 ≤ probeBadE (Ideal.absNorm (Ideal.span {p})) a := by
    unfold probeBadE; positivity
  have hT0 : 0 ≤ probeBadT (Ideal.absNorm (Ideal.span {p})) W := by
    unfold probeBadT; positivity
  have hAi : (1 - probeBadA (Ideal.absNorm (Ideal.span {p})) b)⁻¹ ≤ 2 := by
    have hh : (1 / 2 : ℝ) ≤ 1 - probeBadA (Ideal.absNorm (Ideal.span {p})) b := by linarith
    have hh' := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hh
    simpa only [one_div, inv_div, inv_one, div_one, inv_inv] using hh'
  have hVi : (1 - ‖V‖)⁻¹ ≤ 2 := by
    have hh : (1 / 2 : ℝ) ≤ 1 - ‖V‖ := by linarith
    have hh' := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hh
    simpa only [one_div, inv_div, inv_one, div_one, inv_inv] using hh'
  have hfirst := probeBadPrimeFirst_norm_le K p hp χ hχ hminus j a b W V (by linarith)
  have htail := probeBadPrimeTail_norm_le K p hp χ hχ hminus j a b W V (by linarith) (by linarith)
  have hf : ‖∑' m : ℕ, probeBadPrimeWeight K p hp.ne_zero χ j a b W V 1 0 1 m‖ ≤
      2 * (probeBadE (Ideal.absNorm (Ideal.span {p})) a *
        probeBadT (Ideal.absNorm (Ideal.span {p})) W) := by
    calc
      _ ≤ _ := hfirst
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_left hVi (mul_nonneg hE0 hT0) using 1
        ring
  have ht : ‖probeBadPrimeTail K p hp.ne_zero χ j a b W V‖ ≤
      4 * ((1 + probeBadE (Ideal.absNorm (Ideal.span {p})) a) *
        (1 + probeBadT (Ideal.absNorm (Ideal.span {p})) W) *
        probeBadA (Ideal.absNorm (Ideal.span {p})) b) := by
    calc
      _ ≤ _ := htail
      _ ≤ _ := by
        have hi := mul_le_mul hAi hVi (inv_nonneg.mpr (by linarith)) (by norm_num : (0 : ℝ) ≤ 2)
        have hC : 0 ≤ (1 + probeBadE (Ideal.absNorm (Ideal.span {p})) a) *
            (1 + probeBadT (Ideal.absNorm (Ideal.span {p})) W) *
            probeBadA (Ideal.absNorm (Ideal.span {p})) b := by positivity
        convert mul_le_mul_of_nonneg_left hi hC using 1
        ring
  rw [probeBadPrimeCorrection_sub_one K p hp χ hχ hminus j hj a b W V (by linarith) (by linarith), norm_mul]
  have hnorm : ‖1 - V‖ ≤ 2 := ArtinMatthews.probe_one_sub_norm_upper hV
  calc
    _ ≤ 2 * (‖∑' m : ℕ, probeBadPrimeWeight K p hp.ne_zero χ j a b W V 1 0 1 m‖ +
        ‖probeBadPrimeTail K p hp.ne_zero χ j a b W V‖) :=
      mul_le_mul hnorm (norm_add_le _ _) (norm_nonneg _) (by norm_num)
    _ ≤ _ := by linarith

end
end ArtinMatthews.VaryingKummerAnalytic
