module

public import ArtinMatthews.SourceReflectionDirichlet
public import ArtinMatthews.SourceThetaProfileSmoothing
public import ArtinMatthews.SourceReflectionDirichletMajorant
public import ArtinMatthews.SourceThetaSmoothingSum
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Absolute convergence permits termwise reflected Gaussian smoothing
with the literal frozen/cube/column length. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain MeasureTheory SourceReflection
open scoped NumberField
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (f : Finset (SourceExteriorPrime F S₀))
local notation "I" => SourceReflectionTermIndex F S₀ f

theorem sourceReflectionGaussianProfile_tsum
    (C₀ A₀ : ℝ) (r : ℕ) {σ C : ℝ} (hσ : 1/2 < σ) (hC : 0 ≤ C)
    (a : I → ℂ) (ha : ∀ i, ‖a i‖ ≤ sourceReflectionDirichletTerm F S₀ f 0 i)
    (H : I → ℝ → ℂ) (hm : ∀ i, Measurable (fun t : ℝ => H i (Real.exp t)))
    (hb : ∀ i u, 0 < u → ‖H i u‖ ≤ C * u^(-σ)) {T : ℝ} (hT : 0 < T) :
    sourceThetaGaussianProfile C₀ A₀ r (-1)
      (fun t => ∑' i : I, a i * H i (sourceReflectionTermLength F S₀ i.1.val i.2.1 i.2.2.val * t))
      T =
      ∑' i : I, a i * sourceThetaGaussianProfile C₀ A₀ r (-1) (H i)
        (sourceReflectionTermLength F S₀ i.1.val i.2.1 i.2.2.val * T) := by
  let _ : Countable I := sourceReflectionTermIndex_countable F S₀ f
  let L (i : I) := sourceReflectionTermLength F S₀ i.1.val i.2.1 i.2.2.val
  let x := Real.log T
  let v (i : I) := Real.log (L i)
  let A (_ : I) (t : ℝ) := C * Real.exp (-σ*t)
  let G (i : I) (t : ℝ) := H i (Real.exp t)
  have hL (i : I) : 0 < L i := zero_lt_one.trans_le (sourceReflectionTermLength_one_le F S₀ _ _ _)
  have hx : Real.exp x = T := Real.exp_log hT
  have hv (i : I) : Real.exp (v i) = L i := Real.exp_log (hL i)
  have hA (i : I) : Measurable (A i) := by unfold A; fun_prop
  have hA₀ (i : I) (t : ℝ) : 0 ≤ A i t := mul_nonneg hC (Real.exp_pos _).le
  have hD : Summable (fun i => ‖a i‖ * Real.exp (-σ * v i)) := by
    refine (sourceReflectionCoefficient_summable F S₀ f hσ a ha).congr ?_
    intro i
    change ‖a i‖ * L i ^ (-σ) = ‖a i‖ * Real.exp (-σ * Real.log (L i))
    rw [Real.rpow_def_of_pos (hL i), mul_comm (Real.log (L i))]
  have hGA (i : I) (t : ℝ) : ‖G i t‖ ≤ A i t := by
    have h := hb i (Real.exp t) (Real.exp_pos _)
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm t] at h
    exact h
  have hsum := sourceThetaGaussianLogSmooth_sum_integral C₀ A₀ r (-1) σ C x a v A
    hA hA₀ (fun _ _ => le_rfl) hD G hm hGA
  let V (t : ℝ) := ∑' i : I, a i * H i (L i * t)
  change sourceThetaGaussianProfile C₀ A₀ r (-1) V T = _
  calc
    _ = sourceThetaGaussianLogSmooth C₀ A₀ r (-1) (fun y => V (Real.exp y)) x := by
      have h := sourceThetaGaussianProfile_exp C₀ A₀ r (-1) V x
      rwa [hx] at h
    _ = ∫ y : ℝ, sourceThetaGaussianLogKernel C₀ A₀ r y *
        (∑' i : I, a i * G i (x + v i + (-1)*y)) := by
      unfold sourceThetaGaussianLogSmooth
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        apply congrArg (fun z : ℂ => sourceThetaGaussianLogKernel C₀ A₀ r y * z)
        change V (Real.exp (x + (-1)*y)) = _
        apply tsum_congr
        intro i
        change a i * H i (L i * Real.exp (x + (-1)*y)) =
          a i * H i (Real.exp (x + v i + (-1)*y))
        rw [show x + v i + (-1)*y = v i + (x + (-1)*y) by ring, Real.exp_add (v i) (x + (-1)*y), hv i]
    _ = ∑' i : I, a i * sourceThetaGaussianLogSmooth C₀ A₀ r (-1) (G i) (x + v i) := hsum
    _ = _ := by
      apply tsum_congr
      intro i
      have h := sourceThetaGaussianProfile_exp C₀ A₀ r (-1) (H i) (x + v i)
      rw [Real.exp_add, hx, hv i, mul_comm T] at h
      rw [h]

end
end ArtinMatthews.SourceEulerAssembly
