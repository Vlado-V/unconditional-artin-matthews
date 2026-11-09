module

public import ArtinMatthews.HeckeCubicPrimeSharp
public import ArtinMatthews.HeckeDirichletProduct


set_option backward.privateInPublic true
@[expose] public section

/-! Closed integer subintervals and the fixed extra Dirichlet factor in
the actual long-frequency prime estimate. -/

noncomputable section
namespace ArtinMatthews
open OAI OAI.SevenEighths Filter
open scoped BigOperators Classical

def heckePrimeIntervalSum (η : HeckeFamily.Character) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (m n : ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ (Finset.Icc m n).filter Nat.Prime,
    idealThetaCoeff η p*χ p*(p : ℂ)^((t : ℂ)*Complex.I)

theorem heckePrimeIntervalSum_eq (η : HeckeFamily.Character) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (m n : ℕ) (hmn : m ≤ n) (t : ℝ) :
    heckePrimeIntervalSum η χ m n t =
      heckePrimePhaseCoefficient η χ t m+heckeSharpPrimeSum η χ m n t := by
  unfold heckePrimeIntervalSum heckeSharpPrimeSum
  rw [Finset.sum_filter, Finset.Icc_eq_cons_Ioc hmn, Finset.sum_cons, Finset.sum_filter]
  rfl

theorem cubicNumeratorPrimeInterval_all_log (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3 = (A : OAI.CubicFirstMoment.Eisenstein))
    (A₀ B δ D : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) (hD : 0 < D) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x)^A₀ →
      ∀ (χ : DirichletCharacter ℂ q) (H : ℝ), x^δ ≤ H →
      ∀ m n : ℕ, m ≤ n → H ≤ m → (n : ℝ) ≤ 2*H →
      ∀ t : ℝ, |t| ≤ x^B →
      ‖heckePrimeIntervalSum (cubicNumeratorHeckeCharacter A hA) χ m n t‖ ≤
        35*H*(Real.log x)^(-D) := by
  filter_upwards [cubicNumeratorPrimeSharp_all_log A hA hnoncube A₀ B δ D hB hδ hD,
    heckePrime_uniform_power_log_saving 2 0 δ D (by norm_num) (by norm_num) hδ]
    with x hsharp hconst
  intro q _ hq χ H hH m n hmn hmH hnH t ht
  rw [heckePrimeIntervalSum_eq _ χ m n hmn t]
  have h2 : 2 ≤ H*(Real.log x)^(-D) := by simpa only [Real.rpow_zero, mul_one] using hconst H hH
  have hp := hsharp q hq χ H hH m n hmn hmH hnH t ht
  exact ((norm_add_le _ _).trans (add_le_add
    ((heckePrimePhaseCoefficient_norm_le_two _ χ t m).trans h2) hp)).trans_eq (by ring)

theorem cubicNumeratorPrimeInterval_fixed_twist_all_log (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (A₀ B δ D : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) (hD : 0 < D) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x)^A₀ →
      ∀ (ϑ : DirichletCharacter ℂ q) (H : ℝ), x^δ ≤ H →
      ∀ m n : ℕ, m ≤ n → H ≤ m → (n : ℝ) ≤ 2*H →
      ∀ t : ℝ, |t| ≤ x^B →
      ‖∑ p ∈ (Finset.Icc m n).filter Nat.Prime,
        idealThetaCoeff (cubicNumeratorHeckeCharacter A hA) p*χ p*ϑ p*
          (p : ℂ)^((t : ℂ)*Complex.I)‖ ≤ 35*H*(Real.log x)^(-D) := by
  filter_upwards [cubicNumeratorPrimeInterval_all_log A hA hnoncube (A₀+1) B δ D hB hδ hD,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (r : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with x hbound hr hx
  intro q _ hq ϑ H hH m n hmn hmH hnH t ht
  have hproduct : (r*q : ℝ) ≤ (Real.log x)^(A₀+1) := by
    calc
      _ ≤ Real.log x*(Real.log x)^A₀ := mul_le_mul hr hq (Nat.cast_nonneg q) (Real.log_pos hx).le
      _ = _ := by rw [Real.rpow_add (Real.log_pos hx), Real.rpow_one]; ring
  have h := hbound (r*q) (by exact_mod_cast hproduct) (heckeDirichletProduct χ ϑ)
    H hH m n hmn hmH hnH t ht
  simpa only [heckePrimeIntervalSum, heckeDirichletProduct_natCast, mul_assoc] using h

end ArtinMatthews
