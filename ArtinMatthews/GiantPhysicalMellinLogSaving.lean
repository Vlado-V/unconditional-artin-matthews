module

public import ArtinMatthews.GiantTwoSidedPhysicalMellinPairing
public import ArtinMatthews.MarkedFiniteCells
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! One fixed Mellin window transfers the chosen family's frequency and
absolute-mass bounds. The Fourier order is selected after its mass exponent. -/
namespace ArtinMatthews
open Set Filter MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap ContDiff ComplexConjugate
noncomputable section

universe u v

def giantTwoSidedPhysicalMellinLeftNormalized {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    {Z : Finset ℕ} (X t : ℝ) (f : ℕ → ℂ) (s : GiantTwoSidedEndpointState P M Z) : ℂ :=
  ((X/(s.val.1.val : ℝ) : ℝ) : ℂ)*
    primeExtractionMellinPhase (-t) (s.val.1.val : ℝ)*f s.val.1.val

theorem giantTwoSidedPhysicalMellinLeftNormalized_eq {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    {Z : Finset ℕ} (X t : ℝ) (f : ℕ → ℂ) (s : GiantTwoSidedEndpointState P M Z) :
    giantTwoSidedPhysicalMellinLeftNormalized X t f s =
      (X : ℂ)*giantTwoSidedPhysicalMellinLeft t f s := by
  unfold giantTwoSidedPhysicalMellinLeftNormalized giantTwoSidedPhysicalMellinLeft
  rw [Complex.ofReal_div,Complex.ofReal_natCast]
  ring

theorem giantTwoSidedPhysicalMellinPairing_normalized_eq {J : Type*}
    [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {M : ℕ} {Z : Finset ℕ}
    (A : Matrix (GiantTwoSidedEndpointState P M Z) (GiantTwoSidedEndpointState P M Z) ℂ)
    (f : ℕ → ℂ) (g : GiantTwoSidedEndpointState P M Z → ℂ) {X : ℝ} (hX : 0 < X) (t : ℝ) :
    giantTwoSidedPhysicalWeightedPairing A (giantTwoSidedPhysicalMellinLeftNormalized X t f) g/(X : ℂ) =
      giantTwoSidedPhysicalWeightedPairing A (giantTwoSidedPhysicalMellinLeft t f) g := by
  classical
  have h : markedMatrixPairing A (giantTwoSidedPhysicalMellinLeftNormalized X t f) g =
      (X : ℂ)*markedMatrixPairing A (giantTwoSidedPhysicalMellinLeft t f) g := by
    simp only [markedMatrixPairing_expansion,giantTwoSidedPhysicalMellinLeftNormalized_eq,
      star_mul,Complex.star_def,Complex.conj_ofReal,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro z _
    ring
  unfold giantTwoSidedPhysicalWeightedPairing
  rw [h]
  field_simp [Complex.ofReal_ne_zero.mpr hX.ne']
  <;> ring

theorem giantPhysicalMellin_logSaving_scalar (F : SchwartzMap ℝ ℂ)
    (A B C E : ℝ) (hC : 0 < C) (hB : E+1 < B) :
    ∃ j : ℕ, A+E+1 < C*(j : ℝ) ∧ Integrable (fun t : ℝ => |t|^j*‖F t‖) ∧
      ∀ᶠ x : ℝ in atTop, 0 < x ∧ 1 ≤ Real.log x ∧
        (∫ t : ℝ, ‖F t‖)*(Real.log x)^(-B) +
          ((∫ t : ℝ, |t|^j*‖F t‖)/((Real.log x)^C)^j)*(Real.log x)^A ≤
          (Real.log x)^(-E) := by
  obtain ⟨j,hj⟩ := exists_nat_gt ((A+E+1)/C)
  have hj' : A+E+1 < C*(j : ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ hC).mp hj
  let K₀ := ∫ t : ℝ, ‖F t‖
  let Kⱼ := ∫ t : ℝ, |t|^j*‖F t‖
  have hK₀ : 0 ≤ K₀ := integral_nonneg (fun t => norm_nonneg (F t))
  have hKⱼ : 0 ≤ Kⱼ := integral_nonneg (fun t => mul_nonneg (pow_nonneg (abs_nonneg t) _) (norm_nonneg _))
  refine ⟨j,hj',?_,?_⟩
  · simpa only [Real.norm_eq_abs] using F.integrable_pow_mul volume j
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (K₀+Kⱼ)] with x hx hL hK
  let L := Real.log x
  have hL₀ : 0 < L := zero_lt_one.trans_le hL
  refine ⟨hx,hL,?_⟩
  change K₀*L^(-B)+(Kⱼ/(L^C)^j)*L^A ≤ L^(-E)
  have ht : (Kⱼ/(L^C)^j)*L^A = Kⱼ*L^(A-C*(j : ℝ)) := by
    rw [← Real.rpow_mul_natCast hL₀.le,Real.rpow_sub hL₀]
    ring
  rw [ht]
  calc
    _ ≤ K₀*L^(-E-1)+Kⱼ*L^(-E-1) := add_le_add
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) hK₀)
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) hKⱼ)
    _ = (K₀+Kⱼ)*L^(-E-1) := by ring
    _ ≤ L*L^(-E-1) := mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hL₀.le _)
    _ = L^(1 : ℝ)*L^(-E-1) := by rw [Real.rpow_one]
    _ = L^(-E) := by rw [← Real.rpow_add hL₀]; congr 1; ring

theorem giantTwoSidedPhysicalCutoffPairing_logSaving
    (Ψ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a) (hsupp : Function.support Ψ ⊆ Icc a b)
    (hΨ : ContDiff ℝ ∞ Ψ) (A B C E : ℝ) (hC : 0 < C) (hB : E+1 < B) :
    ∃ j : ℕ, A+E+1 < C*(j : ℝ) ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ {I : Type u} {J : Type v} [Fintype J] [DecidableEq J]
          {P : J → Finset ℕ} {k ell : ℕ} {Z : Finset ℕ},
          (∀ g p, p ∈ P g → p.Prime) → (∀ n ∈ Z, 0 < n) →
          ∀ (patterns : Finset I) (copies : I → J → Finset (Fin k)) (step : ℤ) (q ζ : ℝ)
            (K : ∀ p, GiantTwoSidedPatternCoefficient P (copies p) ell)
            (f : ℕ → ℂ) (g : GiantTwoSidedEndpointState P (k+ell) Z → ℂ),
            giantTwoSidedPhysicalMellinAbsoluteMass patterns copies step q ζ K f g ≤ (Real.log x)^A →
            (∀ t ∈ Icc (-((Real.log x)^C)) ((Real.log x)^C),
              ‖giantTwoSidedPhysicalWeightedPairing
                (giantTwoSidedPhysicalFamilyMatrix patterns copies step q (ζ-2*Real.pi*t) K)
                (giantTwoSidedPhysicalMellinLeft t f) g‖ ≤ (Real.log x)^(-B)) →
            ‖giantTwoSidedPhysicalCutoffPairing patterns copies step q ζ K Ψ x f g‖ ≤ (Real.log x)^(-E) := by
  let F : SchwartzMap ℝ ℂ := 𝓕 (primeExtractionLogProfile Ψ ha hsupp hΨ)
  obtain ⟨j,hj,_,hs⟩ := giantPhysicalMellin_logSaving_scalar F A B C E hC hB
  refine ⟨j,hj,?_⟩
  filter_upwards [hs] with x hx
  rcases hx with ⟨hx,hL,hscalar⟩
  intro I J _ _ P k ell Z hP hZ patterns copies step q ζ K f g hmass hwindow
  let L := Real.log x
  have hL₀ : 0 < L := zero_lt_one.trans_le hL
  have hH : 0 < L^C := Real.rpow_pos_of_pos hL₀ _
  have hR : 0 ≤ L^(-B) := Real.rpow_nonneg hL₀.le _
  have ht : 0 ≤ (∫ t : ℝ, |t|^j*‖F t‖)/(L^C)^j :=
    div_nonneg (integral_nonneg (fun t => mul_nonneg (pow_nonneg (abs_nonneg t) _) (norm_nonneg _)))
      (pow_nonneg hH.le _)
  calc
    _ ≤ (∫ t : ℝ, ‖F t‖)*L^(-B) + ((∫ t : ℝ, |t|^j*‖F t‖)/(L^C)^j)*
        giantTwoSidedPhysicalMellinAbsoluteMass patterns copies step q ζ K f g :=
      giantTwoSidedPhysicalCutoffPairing_mellin_norm_le hP hZ patterns copies step q ζ K
        Ψ ha hsupp hΨ hx hH hR j f g hwindow
    _ ≤ (∫ t : ℝ, ‖F t‖)*L^(-B) + ((∫ t : ℝ, |t|^j*‖F t‖)/(L^C)^j)*L^A :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hmass ht)
    _ ≤ _ := hscalar

end
end ArtinMatthews
