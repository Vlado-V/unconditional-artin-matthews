module

public import ArtinMatthews.VaryingKummerAnalyticHeckeGaussianDetector
public import ArtinMatthews.VaryingKummerAnalyticDedekindSeriesPartialComplex
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The vertical derivative and large Gaussian-energy count for the actual
general-field finite Hecke polynomials. The logarithmic loss is explicit and
the constants are uniform in the conductor, coefficient family, and height. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal MeasureTheory Complex
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def coefficientClassLogWeight
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (c : ClassGroup (𝓞 K))
    (J : integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)) : ℂ :=
  (-I * (Real.log (FractionalIdeal.absNorm J.val.val : ℝ) : ℂ)) * v c J

theorem coefficientClassDirichletPolynomial_hasDerivAt
    (a : integralFractionalIdeals K → ℂ)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ t : ℝ) :
    HasDerivAt (coefficientClassDirichletPolynomial K a B v σ)
      (coefficientClassDirichletPolynomial K a B (coefficientClassLogWeight K v) σ t) t := by
  unfold coefficientClassDirichletPolynomial coefficientClassPolynomial coefficientClassLogWeight
  apply HasDerivAt.fun_sum
  intro c _
  apply HasDerivAt.fun_sum
  intro J _
  convert ((heckeVerticalPhase_hasDerivAt
    (FractionalIdeal.absNorm J.val.val : ℝ) σ t).const_mul (v c J)).mul_const
      (a ⟨J.val,J.property.1⟩) using 1
  ring

theorem coefficientClassDirichletPolynomial_deriv
    (a : integralFractionalIdeals K → ℂ)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ t : ℝ) :
    deriv (coefficientClassDirichletPolynomial K a B v σ) t =
      coefficientClassDirichletPolynomial K a B (coefficientClassLogWeight K v) σ t :=
  (coefficientClassDirichletPolynomial_hasDerivAt K a B v σ t).deriv

theorem coefficientClassLogWeight_mass_le
    {X : ℝ} (hX : 1 ≤ X)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (hB : ∀ c, ∀ J ∈ B c, (FractionalIdeal.absNorm J.val.val:ℝ) ≤ X)
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ : ℝ) :
    coefficientClassDirichletMass K B (coefficientClassLogWeight K v) σ ≤
      (Real.log X)^2 * coefficientClassDirichletMass K B v σ := by
  unfold coefficientClassDirichletMass
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  apply Finset.sum_le_sum
  intro J hJ
  have hN := integralFractionalIdeals_absNorm_ge_one ⟨J.val,J.property.1⟩
  have hlog : |Real.log (FractionalIdeal.absNorm J.val.val : ℝ)| ≤ Real.log X := by
    rw [abs_of_nonneg (Real.log_nonneg hN)]
    exact Real.log_le_log (fractionalIdeal_absNorm_pos J.val) (hB c J hJ)
  have hsq := (sq_le_sq₀ (abs_nonneg _) (Real.log_nonneg hX)).mpr hlog
  simp only [coefficientClassLogWeight,norm_mul,norm_neg,norm_I,Complex.norm_real,
    Real.norm_eq_abs,one_mul]
  convert mul_le_mul_of_nonneg_right hsq
    (sq_nonneg (‖v c J‖ * (FractionalIdeal.absNorm J.val.val : ℝ)^(-σ))) using 1
  ring

def coefficientClassGaussianDerivativeEnergy (a : integralFractionalIdeals K → ℂ)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ t₀ : ℝ) : ℝ :=
  ∫ t : ℝ, Real.exp (-2*t^2) *
    ‖deriv (coefficientClassDirichletPolynomial K a B v σ) (t+t₀)‖^2

theorem coefficientClassGaussianDerivativeEnergy_eq
    (a : integralFractionalIdeals K → ℂ)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ t₀ : ℝ) :
    coefficientClassGaussianDerivativeEnergy K a B v σ t₀ =
      coefficientClassGaussianEnergy K a B (coefficientClassLogWeight K v) σ t₀ := by
  unfold coefficientClassGaussianDerivativeEnergy coefficientClassGaussianEnergy
  simp only [coefficientClassDirichletPolynomial_deriv]

theorem actualHecke_coefficientFamily_gaussian_derivative_sieve
    {U X : ℝ} (hU : 1 ≤ U) (hX : 1 ≤ X)
    (T : Finset (IdealConductorModulus K))
    (hT : ∀ M ∈ T, (Ideal.absNorm M.val:ℝ) ≤ U)
    (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val))
    (hA : ∀ M ∈ T, ∀ ψ ∈ A M, IsPrimitiveOnIdeals ψ.residue)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (hB : ∀ c, ∀ J ∈ B c, (FractionalIdeal.absNorm J.val.val:ℝ) ≤ X)
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ t₀ : ℝ) :
    (∑ M ∈ T, ∑ a ∈ (A M).image (fun ψ => ψ.coefficient),
      coefficientClassGaussianDerivativeEnergy K a B v σ t₀) ≤
      (Real.sqrt (Real.pi/2) *
        ((NumberField.classNumber K:ℝ) * heckeConductorClassConstant K * (X+U^2))) *
          ((Real.log X)^2 * coefficientClassDirichletMass K B v σ) := by
  simp only [coefficientClassGaussianDerivativeEnergy_eq]
  have H := actualHecke_coefficientFamily_gaussian_sieve K hU hX T hT A hA B hB
    (coefficientClassLogWeight K v) σ t₀
  apply H.trans
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_left (coefficientClassLogWeight_mass_le K hX B hB v σ)
  have hC := (heckeConductorClassConstant_pos K).le
  positivity

/-- The exceptional set is constructed from the actual coefficient image;
its cardinal estimate is a consequence of the proved energy bound. -/
theorem actualHecke_coefficientFamily_large_gaussian_energy_count
    {U X : ℝ} (hU : 1 ≤ U) (hX : 1 ≤ X)
    (T : Finset (IdealConductorModulus K))
    (hT : ∀ M ∈ T, (Ideal.absNorm M.val:ℝ) ≤ U)
    (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val))
    (hA : ∀ M ∈ T, ∀ ψ ∈ A M, IsPrimitiveOnIdeals ψ.residue)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (hB : ∀ c, ∀ J ∈ B c, (FractionalIdeal.absNorm J.val.val:ℝ) ≤ X)
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ t₀ δ : ℝ) (hδ : 0 < δ) :
    (∑ M ∈ T, (((A M).image (fun ψ => ψ.coefficient)).filter
      (fun a => δ^2 ≤ coefficientClassGaussianEnergy K a B v σ t₀)).card : ℝ) ≤
      (Real.sqrt (Real.pi/2) *
        (((NumberField.classNumber K:ℝ) * heckeConductorClassConstant K * (X+U^2)) *
          coefficientClassDirichletMass K B v σ)) / δ^2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hδ)).mpr
  calc
    _ ≤ ∑ M ∈ T, ∑ a ∈ (A M).image (fun ψ => ψ.coefficient),
        coefficientClassGaussianEnergy K a B v σ t₀ := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro M _
      calc
        _ = ∑ a ∈ (((A M).image (fun ψ => ψ.coefficient)).filter
            (fun a => δ^2 ≤ coefficientClassGaussianEnergy K a B v σ t₀)), δ^2 := by
          simp
        _ ≤ ∑ a ∈ (((A M).image (fun ψ => ψ.coefficient)).filter
            (fun a => δ^2 ≤ coefficientClassGaussianEnergy K a B v σ t₀)),
              coefficientClassGaussianEnergy K a B v σ t₀ := by
          exact Finset.sum_le_sum fun a ha => (Finset.mem_filter.mp ha).2
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun a _ _ => coefficientClassGaussianEnergy_nonneg K a B v σ t₀)
    _ ≤ _ := actualHecke_coefficientFamily_gaussian_sieve K hU hX T hT A hA B hB v σ t₀

end
end ArtinMatthews.VaryingKummerAnalytic
