module

public import ArtinMatthews.ReflectionCoefficientGaussBound
public import ArtinMatthews.SourcePrimeExponentProducts
public import Mathlib.Analysis.Normed.Ring.InfiniteSum


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute convergence of the literal coefficient row. A direct
finite-Gauss bound and a genuine Dedekind majorant suffice here; no
reflected moment or primitive Gauss norm is used as an input. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

theorem reflectionExponentNorm_smul (e : SourcePrimeExponents F S₀) (k : ℕ) :
    sourcePrimeExponentNorm F S₀ (k • e) = sourcePrimeExponentNorm F S₀ e ^ k := by
  induction k with
  | zero => simp only [zero_smul, sourcePrimeExponentNorm_zero, pow_zero]
  | succ k ih => rw [add_smul, one_smul, sourcePrimeExponentNorm_add, ih, pow_succ]

theorem reflectionExponentNorm_cube_ge_product (c n : SourcePrimeExponents F S₀) :
    (sourcePrimeExponentNorm F S₀ c : ℝ) * (sourcePrimeExponentNorm F S₀ n : ℝ) ≤
      sourcePrimeExponentNorm F S₀ (c + 3 • n) := by
  have hn : 1 ≤ sourcePrimeExponentNorm F S₀ n := sourcePrimeExponentNorm_pos F S₀ n
  rw [sourcePrimeExponentNorm_add, reflectionExponentNorm_smul, Nat.cast_mul, Nat.cast_pow]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hnr : (1 : ℝ) ≤ sourcePrimeExponentNorm F S₀ n := Nat.one_le_cast.mpr hn
  exact le_self_pow₀ hnr (by decide)

variable [IsTotallyComplex F]
    (hS : QuadraticWeil.standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)

theorem reflectionCoefficientTerm_norm_le_gaussian
    (c : ReflectionSquarefreeExponents F S₀) (n : SourcePrimeExponents F S₀)
    (m : sourceRing F S₀) (Z : ℝ) :
    ‖reflectionCoefficientTerm F hζ S₀ hS η c n m Z‖ ≤
      reflectionGaussian ((sourcePrimeExponentNorm F S₀ (c.val + 3 • n) : ℝ) / Z) := by
  have hc : 0 < (sourcePrimeExponentNorm F S₀ c.val : ℝ) :=
    Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ c.val)
  have hn : (1 : ℝ) ≤ sourcePrimeExponentNorm F S₀ n :=
    Nat.one_le_cast.mpr (sourcePrimeExponentNorm_pos F S₀ n)
  have hroot := Real.sqrt_pos.mpr hc
  have hratio : ‖reflectionGammaTwo F hζ S₀ c.val‖ /
      (Real.sqrt (sourcePrimeExponentNorm F S₀ c.val : ℝ) *
        (sourcePrimeExponentNorm F S₀ n : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (mul_pos hroot (lt_of_lt_of_le zero_lt_one hn))).mpr
    rw [one_mul]
    exact (reflectionGammaTwo_norm_le_sqrt F hζ S₀ c.val).trans
      (le_mul_of_one_le_right hroot.le hn)
  have htheta := reflectionThetaValue_norm_le_one F hζ S₀ hS η (c.val + 3 • n)
  have hres := reflectionExponentResidueValue_norm_le_one F hζ S₀ (c.val + 3 • n) m
  have hproduct :
      (‖reflectionGammaTwo F hζ S₀ c.val‖ /
        (Real.sqrt (sourcePrimeExponentNorm F S₀ c.val : ℝ) *
          (sourcePrimeExponentNorm F S₀ n : ℝ)) *
        ‖reflectionThetaValue F hζ S₀ hS η (c.val + 3 • n)‖) *
        ‖reflectionExponentResidueValue F hζ S₀ (c.val + 3 • n) m‖ ≤ 1 := by
    calc
      _ ≤ (1 * 1) * 1 :=
        mul_le_mul (mul_le_mul hratio htheta (norm_nonneg _) zero_le_one) hres
          (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  unfold reflectionCoefficientTerm
  dsimp only
  rw [norm_mul, norm_mul, norm_mul, norm_div, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Complex.norm_natCast, Complex.norm_real,
    Real.norm_of_nonneg (reflectionGaussian_pos _).le]
  exact mul_le_of_le_one_left (reflectionGaussian_pos _).le hproduct

theorem reflectionCoefficientTerm_dedekind_majorant
    (c : ReflectionSquarefreeExponents F S₀) (n : SourcePrimeExponents F S₀)
    (m : sourceRing F S₀) {Z : ℝ} (hZ : 0 < Z) :
    ‖reflectionCoefficientTerm F hζ S₀ hS η c n m Z‖ ≤
      (Real.exp (2 ^ 2 : ℝ) / (2 * Real.sqrt Real.pi)) * Z ^ (2 : ℝ) *
        ((sourcePrimeExponentNorm F S₀ c.val : ℝ) ^ (-2 : ℝ) *
          (sourcePrimeExponentNorm F S₀ n : ℝ) ^ (-2 : ℝ)) := by
  have hc : 0 < (sourcePrimeExponentNorm F S₀ c.val : ℝ) :=
    Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ c.val)
  have hn : 0 < (sourcePrimeExponentNorm F S₀ n : ℝ) :=
    Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ n)
  have hA : 0 < (sourcePrimeExponentNorm F S₀ (c.val + 3 • n) : ℝ) :=
    Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ _)
  have hp := Real.rpow_le_rpow_of_nonpos (mul_pos hc hn)
    (reflectionExponentNorm_cube_ge_product F S₀ c.val n) (show (-2 : ℝ) ≤ 0 by norm_num)
  rw [Real.mul_rpow hc.le hn.le] at hp
  exact (reflectionCoefficientTerm_norm_le_gaussian F hζ S₀ hS η c n m Z).trans
    ((reflectionGaussian_ratio_bound hA hZ 2).trans
      (mul_le_mul_of_nonneg_left hp (by positivity)))

theorem reflectionCoefficientRow_summable_norm (m : sourceRing F S₀)
    {Z : ℝ} (hZ : 0 < Z) :
    Summable (fun p : ReflectionSquarefreeExponents F S₀ × SourcePrimeExponents F S₀ =>
      ‖reflectionCoefficientTerm F hζ S₀ hS η p.1 p.2 m Z‖) := by
  have hs := sourcePrimeExponentNorm_summable F S₀ (σ := 2) (by norm_num)
  have hc : Summable (fun c : ReflectionSquarefreeExponents F S₀ =>
      (sourcePrimeExponentNorm F S₀ c.val : ℝ) ^ (-2 : ℝ)) :=
    hs.subtype (fun c => ∀ P, c P ≤ 1)
  have hp : Summable (fun p : ReflectionSquarefreeExponents F S₀ × SourcePrimeExponents F S₀ =>
      (sourcePrimeExponentNorm F S₀ p.1.val : ℝ) ^ (-2 : ℝ) *
        (sourcePrimeExponentNorm F S₀ p.2 : ℝ) ^ (-2 : ℝ)) :=
    summable_mul_of_summable_norm hc.norm hs.norm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => reflectionCoefficientTerm_dedekind_majorant F hζ S₀ hS η p.1 p.2 m hZ)
    (hp.mul_left ((Real.exp (2 ^ 2 : ℝ) / (2 * Real.sqrt Real.pi)) * Z ^ (2 : ℝ)))

theorem reflectionCoefficientRow_eq_product_tsum (m : sourceRing F S₀)
    {Z : ℝ} (hZ : 0 < Z) :
    reflectionCoefficientRow F hζ S₀ hS η m Z =
      ∑' p : ReflectionSquarefreeExponents F S₀ × SourcePrimeExponents F S₀,
        reflectionCoefficientTerm F hζ S₀ hS η p.1 p.2 m Z := by
  exact (reflectionCoefficientRow_summable_norm F hζ S₀ hS η m hZ).of_norm.tsum_prod.symm

end
end ArtinMatthews.VaryingKummerAnalytic
