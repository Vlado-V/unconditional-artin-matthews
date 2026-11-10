module

public import ArtinMatthews.MarkedMajorScalarProductMean
public import ArtinMatthews.MarkedMajorFourierWeight
public import ArtinMatthews.MarkedMajorLabelPolynomial
public import ArtinMatthews.MarkedMajorEnergyBounded
public import ArtinMatthews.MarkedMajorLabelBounded
public import ArtinMatthews.MarkedMajorLabelLocalMean
public import ArtinMatthews.MarkedMajorMellinLocalMean
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

/-! The actual label polynomial times the two arbitrary normalized scalar
polynomials, and its coarse weighted means on every translated scale. -/
namespace ArtinMatthews
open Filter Finset MeasureTheory
open scoped Topology
noncomputable section

def markedMajorScalarEndpoint {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (η : ℝ → ℂ) {k : ℕ} (χ : DirichletCharacter ℂ k)
    (θ Y H U : ℝ) (S T : Finset ℕ) (α β : ℕ → ℂ) (t : ℝ) : ℂ :=
  markedMajorLabelPolynomial bands η χ θ Y t*
    markedMajorScalarPolynomial S H α t*markedMajorScalarPolynomial T U β t

theorem markedMajorScalarPolynomial_bounded (S : Finset ℕ) (H : ℝ) (a : ℕ → ℂ) :
    ∃ K : ℝ, ∀ t, ‖markedMajorScalarPolynomial S H a t‖ ≤ K :=
  ⟨∑ n ∈ S,‖a n/(H:ℂ)‖, markedNaturalPolynomial_norm_le S _⟩

theorem markedMajorScalarEndpoint_continuous {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (η : ℝ → ℂ) {k : ℕ} (χ : DirichletCharacter ℂ k)
    (θ Y H U : ℝ) (S T : Finset ℕ) (α β : ℕ → ℂ) :
    Continuous (markedMajorScalarEndpoint bands η χ θ Y H U S T α β) := by
  have hlabel : Continuous (markedMajorLabelPolynomial bands η χ θ Y) := by
    unfold markedMajorLabelPolynomial markedPrimePhase
    fun_prop
  exact (hlabel.mul (markedMajorScalarPolynomial_continuous S H α)).mul
    (markedMajorScalarPolynomial_continuous T U β)

theorem markedMajorScalarEndpoint_bounded {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (η : ℝ → ℂ) {k : ℕ} (χ : DirichletCharacter ℂ k)
    (θ Y H U : ℝ) (S T : Finset ℕ) (α β : ℕ → ℂ) :
    ∃ K : ℝ, ∀ t, ‖markedMajorScalarEndpoint bands η χ θ Y H U S T α β t‖ ≤ K := by
  obtain ⟨A,hA⟩ := markedMajorLabelPolynomial_bounded bands η χ θ Y
  obtain ⟨B,hB⟩ := markedMajorScalarPolynomial_bounded S H α
  obtain ⟨C,hC⟩ := markedMajorScalarPolynomial_bounded T U β
  have hA₀ := (norm_nonneg _).trans (hA 0)
  have hB₀ := (norm_nonneg _).trans (hB 0)
  refine ⟨A*B*C,?_⟩
  intro t
  simp only [markedMajorScalarEndpoint,norm_mul]
  exact mul_le_mul (mul_le_mul (hA t) (hB t) (norm_nonneg _) hA₀)
    (hC t) (norm_nonneg _) (mul_nonneg hA₀ hB₀)

theorem markedMajorScalarEndpoint_weighted_mean (σ Cα Cβ : ℝ) (hσ : 0 ≤ σ)
    (η : ℝ → ℂ) (hη : ∀ u,‖η u‖ ≤ 1) {hi : ℝ}
    (hhi : 0 ≤ hi) (hsupp : Function.support η ⊆ Set.Iic hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ {J : Type} [Fintype J] (bands : J → Finset ℕ),
        (∀ j p,p ∈ bands j → p.Prime) →
        Pairwise (fun i j => Disjoint (bands i) (bands j)) →
        (∀ j,0 < bandReciprocalMass (bands j)) →
        ∀ (Y θ H U : ℝ) (S T : Finset ℕ) (α β : ℕ → ℂ),
          0 < Y → 0 < H → 0 < U → 1 ≤ H*U → H*U ≤ Real.exp (σ*L) →
          (∀ m ∈ S,H ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*H) →
          (∀ n ∈ T,U ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*U) →
          (∀ m ∈ S,‖α m‖ ≤ L^Cα) → (∀ n ∈ T,‖β n‖ ≤ L^Cβ) →
          ∀ (k : ℕ) (χ : DirichletCharacter ℂ k) (W c : ℝ), 1 ≤ W →
            (∫ t, markedMajorFourierWeight (W*(H*U)) 2 (t-c)*
              ‖markedMajorScalarEndpoint bands η χ θ Y H U S T α β t‖^2) ≤
              C*W*L^(2*(Cα+Cβ)+5) := by
  obtain ⟨E,hE,hmean⟩ := markedMajorScalarPolynomial_product_mean_log σ Cα Cβ hσ
  let D := 2*(Cα+Cβ)+5
  let C₀ := 2*hi^2*E+1
  refine ⟨markedMajorLocalMeanConstant*C₀,mul_pos markedMajorLocalMeanConstant_pos (by dsimp only [C₀]; positivity),?_⟩
  filter_upwards [hmean,eventually_ge_atTop (1:ℝ)] with L hm hL
  intro J _ bands hP hdis hV Y θ H U S T α β hY hH hU hX hupper hS hT hα hβ k χ W c hW
  let Q := markedMajorScalarEndpoint bands η χ θ Y H U S T α β
  let w := W*(H*U)
  let M := markedMajorScalarPolynomial S H α
  let N := markedMajorScalarPolynomial T U β
  have hW₀ := zero_lt_one.trans_le hW
  have hw : 0 < w := mul_pos hW₀ (mul_pos hH hU)
  have hL₀ := zero_lt_one.trans_le hL
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  have hQc := markedMajorScalarEndpoint_continuous bands η χ θ Y H U S T α β
  obtain ⟨K,hK⟩ := markedMajorScalarEndpoint_bounded bands η χ θ Y H U S T α β
  have hlocal (z : ℝ) : (∫ t in Set.Icc z (z+w), ‖Q t‖^2) ≤ C₀*W*L^D := by
    rw [markedMajor_local_integral_eq_translated _ z w hw.le]
    let ξ := z+w/2
    have hM : Continuous (fun t => M (t+ξ)*N (t+ξ)) :=
      ((markedMajorScalarPolynomial_continuous S H α).mul
        (markedMajorScalarPolynomial_continuous T U β)).comp (continuous_id.add continuous_const)
    have hQi : IntegrableOn (fun t => ‖Q (t+ξ)‖^2) (Set.Icc (-(w/2)) (w/2)) :=
      ((hQc.comp (continuous_id.add continuous_const)).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc
    have hMi : IntegrableOn (fun t => ‖M (t+ξ)*N (t+ξ)‖^2) (Set.Icc (-(w/2)) (w/2)) :=
      (hM.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    have hnorm (t : ℝ) : ‖Q (t+ξ)‖^2 ≤ hi^2*‖M (t+ξ)*N (t+ξ)‖^2 := by
      unfold Q markedMajorScalarEndpoint
      rw [mul_assoc,norm_mul,mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (markedMajorLabelPolynomial_norm_le bands hP hdis hV
          η hhi hη hsupp χ θ Y (t+ξ) hY) 2) (sq_nonneg _)
    have hraw := hm S T H U (w/2) ξ α β hH hU (by positivity) hX hupper hS hT hα hβ
    have hwdiv : (w/2)/(H*U)=W/2 := by
      dsimp only [w]
      field_simp
    rw [hwdiv] at hraw
    have hpow : L^(2*(Cα+Cβ)+3) ≤ L^D :=
      Real.rpow_le_rpow_of_exponent_le hL (by dsimp only [D]; linarith)
    calc
      _ ≤ ∫ t in Set.Icc (-(w/2)) (w/2), hi^2*‖M (t+ξ)*N (t+ξ)‖^2 :=
        integral_mono hQi (hMi.const_mul (hi^2)) hnorm
      _ = hi^2*(∫ t in Set.Icc (-(w/2)) (w/2), ‖M (t+ξ)*N (t+ξ)‖^2) := integral_const_mul _ _
      _ ≤ hi^2*(E*L^(2*(Cα+Cβ)+3)*(1+W/2)) := mul_le_mul_of_nonneg_left hraw (sq_nonneg _)
      _ ≤ hi^2*(E*L^D*(2*W)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hE.le) (by linarith) (by positivity) (by positivity)
      _ = (2*hi^2*E)*W*L^D := by ring
      _ ≤ C₀*W*L^D := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL₀.le _)
        exact mul_le_mul_of_nonneg_right (by dsimp only [C₀]; linarith) hW₀.le
  have hh := markedMajorLocalMean_weighted Q hQc K hK hw
    (show 0 ≤ C₀*W*L^D from mul_nonneg (mul_nonneg hC₀ hW₀.le) (Real.rpow_nonneg hL₀.le _)) hlocal c
  exact hh.trans_eq (by ring)

end
end ArtinMatthews
