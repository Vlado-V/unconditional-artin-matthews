module

public import ArtinMatthews.HeckeCubicPrimeSmooth
public import ArtinMatthews.HeckeDirichletProduct


set_option backward.privateInPublic true
@[expose] public section

/-! The fixed extra Dirichlet character in the actual smooth prime estimate,
with its product modulus and literal values proved at every integer. -/

noncomputable section
namespace ArtinMatthews
open OAI OAI.SevenEighths Filter
open scoped ContDiff Topology

theorem cubicNumeratorPrimeSmooth_fixed_twist_all_log (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (A₀ B δ D : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x)^A₀ →
      ∀ (ϑ : DirichletCharacter ℂ q) (H : ℝ), x^δ ≤ H →
      ∀ t : ℝ, |t| ≤ x^B →
      ‖∑' p : ℕ, if p.Prime then
        idealThetaCoeff (cubicNumeratorHeckeCharacter A hA) p*χ p*ϑ p*
          W ((p : ℝ)/H)*(p : ℂ)^((t : ℂ)*Complex.I) else 0‖ ≤
        H*(Real.log x)^(-D) := by
  filter_upwards [cubicNumeratorPrimeSmooth_all_log A hA hnoncube W a b ha hsupp hW
    (A₀+1) B δ D hB hδ,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (r : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with x hbound hr hx
  intro q _ hq ϑ H hH t ht
  have hproduct : (r*q : ℝ) ≤ (Real.log x)^(A₀+1) := by
    calc
      _ ≤ Real.log x*(Real.log x)^A₀ := mul_le_mul hr hq
        (Nat.cast_nonneg q) (Real.log_pos hx).le
      _ = _ := by rw [Real.rpow_add (Real.log_pos hx), Real.rpow_one]; ring
  have h := hbound (r*q) (by exact_mod_cast hproduct) (heckeDirichletProduct χ ϑ) H hH t ht
  simpa only [heckeRationalPrimeSmoothSum, heckeDirichletProduct_natCast, mul_assoc] using h

end ArtinMatthews
