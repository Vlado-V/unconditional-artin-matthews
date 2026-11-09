module

public import ArtinMatthews.SourceComparisonLowTime
public import ArtinMatthews.SourceComparisonMellinTest
public import ArtinMatthews.SourceComparisonGiantCenter


set_option backward.privateInPublic true
@[expose] public section

/-! The ordinary comparison endpoint, with its literal inert factor and
centered giant-prime statistic, has the finite low-frequency bound. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

variable {J G : Type*} [Fintype J] [Fintype G]

def sourceComparisonCenteredEndpoint (e : J → ℝ) (ε x Y σ : ℝ) (ψ : ℝ → ℂ)
    (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (n : ℕ) : ℂ :=
  ψ ((n : ℝ) / Y) * (n : ℂ) ^ ((σ : ℂ) * Complex.I) *
    giantCandidateFirstEndpoint e ε x n * sourceComparisonMarkWeight P t q b n

def sourceComparisonCenteredMellinSum (e : J → ℝ) (ε x Y σ B : ℝ) (ψ : ℝ → ℂ)
    (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (k : ℕ) [NeZero k] (h : ℤ) (τ : ℝ) : ℂ :=
  (∑ n ∈ Ioc 0 ⌊B * Y⌋₊, sourceComparisonCenteredEndpoint e ε x Y σ ψ P t q b n *
    sourceComparisonRationalPhase k h (n : ZMod k) * (n : ℂ) ^ ((τ : ℂ) * Complex.I)) / (Y : ℂ)

theorem sourceComparisonCenteredMellinSum_bound (e : J → ℝ)
    (ε x Y σ B : ℝ) (ψ : ℝ → ℂ)
    (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ)
    (hb : ∀ l ∈ sourceComparisonMarkChoices P t, ‖b l‖ ≤ 1)
    (k : ℕ) [NeZero k] (h : ℤ) (τ : ℝ) (j : ℕ)
    {a b₀ Z M M₁ : ℝ} (ha : 0 < a) (hab : a ≤ b₀) (hB : b₀ < B) (hY : 0 < Y)
    (hψ : ContDiff ℝ 1 ψ) (hs : ∀ z ∉ Set.Icc a b₀, ψ z = 0)
    (hM : 0 ≤ M) (hM₁ : 0 ≤ M₁) (h0 : ∀ z, ‖ψ z‖ ≤ M) (h1 : ∀ z, ‖deriv ψ z‖ ≤ M₁)
    (hcap : ∀ n ∈ Ioc 0 ⌊B * Y⌋₊, giantMarkedCenteredCore ε x n =
      (giantWindowDivisorCount (giantPrimeWindow x ε) n -
        ∑ p ∈ giantPrimeWindow x ε, 1 / (p : ℝ) : ℝ))
    (hCx : 0 ≤ giantPrimeReciprocalSum x ε ∧ giantPrimeReciprocalSum x ε ≤ 1)
    (hq : ∀ g, 0 ≤ q g ∧ q g ≤ 1)
    (hΛ : ∀ p ∈ giantPrimeWindow x ε, p.Prime) (hZ : 1 ≤ Z) :
    let Q := Sum.elim (fun i => markedLogPowerBand (e i) x) P
    let u := Sum.elim (fun _ => 1) t
    let Λ := giantPrimeWindow x ε
    Pairwise (fun i i' => Disjoint (Q i) (Q i')) →
    (∀ p ∈ univ.biUnion Q, p.Prime) →
    (∀ i, 0 < bandReciprocalMass (Q i)) →
    (∀ p ∈ univ.biUnion Q, (p : ℝ) ≤ Z) →
    Disjoint Λ (univ.biUnion Q) →
    (∀ p ∈ univ.biUnion Q ∪ Λ, p.Coprime k) →
    ‖sourceComparisonCenteredMellinSum e ε x Y σ B ψ P t q b k h τ‖ ≤
      M * B * Real.sqrt (sourceComparisonDivisorErrorBudget Q u j) +
        ((((Λ.card : ℝ) + sourceComparisonLongReciprocal Λ) / Y) *
          ((3 * (k : ℝ)) * (B * (M₁ + M * |σ + τ| / a)))) *
          (Real.exp (∑ p ∈ univ.biUnion Q, 1 / (p : ℝ)) * Z ^ ((∑ g, u g) + j)) := by
  classical
  intro Q u Λ hdis hQ hV hQZ hsep hk
  let r : J ⊕ G → ℝ := Sum.elim (fun _ => 1/2) q
  let b' (l : (g : J ⊕ G) → Fin (u g) → ℕ) : ℂ := b (fun g => l (.inr g))
  let f := sourceComparisonMellinTest ψ Y (σ + τ)
  let I := Ioc 0 ⌊B * Y⌋₊
  let A := sourceComparisonRationalPhase k h
  have hb' : ∀ l ∈ sourceComparisonMarkChoices Q u, ‖b' l‖ ≤ 1 := by
    intro l hl
    apply hb
    have hc := (mem_sourceComparisonMarkChoices Q u l).mp hl
    exact (mem_sourceComparisonMarkChoices P t (fun g => l (.inr g))).mpr
      ⟨fun g i => hc.1 (.inr g) i, fun g => hc.2 (.inr g)⟩
  have hr (g : J ⊕ G) : 0 ≤ r g ∧ r g ≤ 1 := by
    rcases g with g | g
    · change 0 ≤ (1/2:ℝ) ∧ (1/2:ℝ) ≤ 1
      norm_num
    · exact hq g
  have hCeq (n : ℕ) (hn : n ∈ I) :
      sourceComparisonLongCenter Λ n = (giantMarkedCenteredCore ε x n : ℂ) := by
    rw [hcap n hn]
    rfl
  have hC (n : ℕ) (hn : n ∈ I) : ‖sourceComparisonLongCenter Λ n‖ ≤ 1 := by
    rw [hCeq n hn, giantMarkedCenteredCore, Complex.norm_real, Real.norm_eq_abs]
    exact boundedGiantIndicator_sub_abs_le_one n x ε _ hCx.1 hCx.2
  have hs₀ (z : ℝ) (hz : z < a) : ψ z = 0 := hs z (fun h => (not_le_of_gt hz) h.1)
  have hB₀ : 0 ≤ B := (ha.trans_le hab).le.trans hB.le
  have hBY : 0 ≤ B * Y := mul_nonneg hB₀ hY.le
  have hf : ContDiff ℝ 1 f := sourceComparisonMellinTest_contDiff ψ (σ + τ) ha hψ hs₀
  have hfB : f (B * Y) = 0 := by
    dsimp only [f, sourceComparisonMellinTest]
    rw [mul_div_cancel_right₀ _ hY.ne', hs B (fun h => (not_le_of_gt hB) h.2), zero_mul]
  have hf₀ : f 0 = 0 := by
    dsimp only [f, sourceComparisonMellinTest]
    rw [zero_div, hs₀ 0 ha, zero_mul]
  have heq (n : ℕ) (hn : n ∈ I) :
      sourceComparisonCenteredEndpoint e ε x Y σ ψ P t q b n * A (n : ZMod k) *
        (n : ℂ) ^ ((τ : ℂ) * Complex.I) =
      A (n : ZMod k) * f n * sourceComparisonLongCenter Λ n *
        sourceComparisonMarkWeight Q u r b' n := by
    have hn₀ : 0 < n := (mem_Ioc.mp hn).1
    have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn₀
    have hW : sourceComparisonMarkWeight Q u r b' n =
        (literalMarkedArrayWeight e x n : ℂ) * sourceComparisonMarkWeight P t q b n :=
      sourceComparisonInertActiveMarks_eq e x P t q b n
    have hphase : (n : ℂ) ^ ((σ : ℂ) * Complex.I) * (n : ℂ) ^ ((τ : ℂ) * Complex.I) =
        (n : ℂ) ^ (((σ + τ : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn₀.ne'), Complex.ofReal_add, add_mul]
    rw [hW, hCeq n hn, sourceComparisonCenteredEndpoint, giantCandidateFirstEndpoint]
    dsimp only [f]
    rw [sourceComparisonMellinTest_eq_cpow ψ Y (σ + τ) hnR, Complex.ofReal_natCast, ← hphase]
    ring
  have he : sourceComparisonCenteredMellinSum e ε x Y σ B ψ P t q b k h τ =
      (∑ n ∈ I, A (n : ZMod k) * f n * sourceComparisonLongCenter Λ n *
        sourceComparisonMarkWeight Q u r b' n) / (Y : ℂ) := by
    unfold sourceComparisonCenteredMellinSum
    rw [sum_congr rfl heq]
  have hlow := sourceComparisonLowTime_bound Q u r hdis hQ hV hr b' hb' j hZ hQZ Λ hΛ hsep
    k hk A (fun z => (sourceComparisonRationalPhase_norm k h z).le)
    f hBY hM (hf.differentiable (by norm_num)) (hf.continuous_deriv (by norm_num)) hfB hf₀
    (fun n _ => (sourceComparisonMellinTest_norm ψ Y (σ + τ) n).trans_le (h0 _)) hC
  have hfvar := sourceComparisonMellinTest_variation ψ (σ + τ) hY ha hB₀ hM hM₁ hψ hs₀ h0 h1
  let R := Real.exp (∑ p ∈ univ.biUnion Q, 1 / (p : ℝ)) * Z ^ ((∑ g, u g) + j)
  let E := Real.sqrt (sourceComparisonDivisorErrorBudget Q u j)
  have hR : 0 ≤ R := mul_nonneg (Real.exp_pos _).le (pow_nonneg (zero_le_one.trans hZ) _)
  have hΛ₀ : 0 ≤ (Λ.card : ℝ) + sourceComparisonLongReciprocal Λ := by
    unfold sourceComparisonLongReciprocal
    positivity
  have hlow' : ‖∑ n ∈ I, A (n : ZMod k) * f n * sourceComparisonLongCenter Λ n *
      sourceComparisonMarkWeight Q u r b' n‖ ≤
      M * (B * Y) * E +
        (((Λ.card : ℝ) + sourceComparisonLongReciprocal Λ) *
          (3 * (k : ℝ) * (B * (M₁ + M * |σ + τ| / a)))) * R := by
    refine hlow.trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Nat.floor_le hBY) hM)
        (Real.sqrt_nonneg _)
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfvar (by positivity)) hΛ₀) hR
  rw [he, norm_div, Complex.norm_real, Real.norm_of_nonneg hY.le]
  apply (div_le_div_of_nonneg_right hlow' hY.le).trans_eq
  change (_ + _) / Y = M * B * E +
    (((((Λ.card : ℝ) + sourceComparisonLongReciprocal Λ) / Y) *
      ((3 * (k : ℝ)) * (B * (M₁ + M * |σ + τ| / a)))) * R)
  field_simp

end
end ArtinMatthews
