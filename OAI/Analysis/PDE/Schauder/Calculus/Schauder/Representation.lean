module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.PoissonInverse
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Order.CompletePartialOrder
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
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Poisson
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.PoissonSharp
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.PotentialDerivatives


set_option backward.privateInPublic true
@[expose] public section

/-! The Newtonian inverse is also a left inverse on compactly supported C² functions. -/

noncomputable section
open _root_.MeasureTheory Set Metric InnerProductSpace Laplacian
namespace OAI.Analysis.PDE.Schauder

theorem newtonianPotential_laplacian {m : ℕ} (hm : 2 ≤ m)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u)
    (x : EuclideanSpace ℝ (Fin m)) :
    newtonianPotential (laplacian u) x = poissonNormalization m * u x := by
  have hD : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hDD : Continuous (fderiv ℝ (fderiv ℝ u)) := hD.continuous_fderiv one_ne_zero
  have hi (i : Fin m) : Integrable (fun y => newtonianKernel m y *
      fderiv ℝ (fderiv ℝ u) (x - y) (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single i (1 : ℝ))) := by
    apply newtonianPotential_integrable (show 1 ≤ m by omega)
      (fun y => fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single i (1 : ℝ))) _ _ x
    · exact (hDD.clm_apply continuous_const).clm_apply continuous_const
    · exact ((huc.fderiv ℝ).fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))).comp_left
        (g := fun L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ => L (EuclideanSpace.single i (1 : ℝ))) (by simp)
  calc
    _ = ∫ y, ∑ i : Fin m, newtonianKernel m y *
        fderiv ℝ (fderiv ℝ u) (x - y) (EuclideanSpace.single i (1 : ℝ))
          (EuclideanSpace.single i (1 : ℝ)) := by
      simp only [newtonianPotential, laplacian_coordinate, Finset.mul_sum]
    _ = ∑ i : Fin m, newtonianPotential (fun y => fderiv ℝ (fderiv ℝ u) y
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))) x :=
      integral_finsetSum _ (fun i _ => hi i)
    _ = laplacian (newtonianPotential u) x := by
      rw [laplacian_coordinate]
      apply Finset.sum_congr rfl
      intro i hi
      exact (second_fderiv_newtonianPotential_apply (show 1 ≤ m by omega) u hu huc x _ _).symm
    _ = _ := laplacian_newtonianPotential hm u hu huc x

theorem poissonPotential_laplacian {m : ℕ} (hm : 3 ≤ m)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) :
    poissonPotential (laplacian u) = u := by
  funext x
  change (poissonNormalization m)⁻¹ * newtonianPotential (laplacian u) x = u x
  rw [newtonianPotential_laplacian (show 2 ≤ m by omega) u hu huc,
    ← mul_assoc, inv_mul_cancel₀ (poissonNormalization_ne_zero hm), one_mul]

theorem contDiff_laplacian_of_four {m : ℕ} (u : EuclideanSpace ℝ (Fin m) → ℝ)
    (hu : ContDiff ℝ 4 u) : ContDiff ℝ 2 (laplacian u) := by
  have hD : ContDiff ℝ 3 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hDD : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ u)) := hD.fderiv_right (by norm_num)
  have he : laplacian u = fun x => ∑ i : Fin m, fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) := funext (laplacian_coordinate u)
  rw [he]
  exact ContDiff.sum fun i _ => (hDD.clm_apply contDiff_const).clm_apply contDiff_const

theorem hasCompactSupport_laplacian {m : ℕ} (u : EuclideanSpace ℝ (Fin m) → ℝ)
    (huc : HasCompactSupport u) : HasCompactSupport (laplacian u) := by
  have he : laplacian u = fun x => ∑ i : Fin m, fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) := funext (laplacian_coordinate u)
  rw [he]
  exact ((huc.fderiv ℝ).fderiv ℝ).comp_left
    (g := fun A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ =>
      ∑ i : Fin m, A (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))) (by simp)

theorem compact_schauder_estimate {m : ℕ} (hm : 3 ≤ m)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ (u : EuclideanSpace ℝ (Fin m) → ℝ),
      ContDiff ℝ 4 u → HasCompactSupport u → ∀ H, 0 ≤ H →
      (∀ x y, |laplacian u x - laplacian u y| ≤ H * ‖x - y‖ ^ α) → ∀ x z,
      ‖fderiv ℝ (fderiv ℝ u) z - fderiv ℝ (fderiv ℝ u) x‖ ≤ C * H * ‖z - x‖ ^ α := by
  obtain ⟨C, hC, hb⟩ := poissonPotential_hessian_holder hm hα hα1
  refine ⟨C, hC, ?_⟩
  intro u hu huc H hH hh x z
  have h := hb (laplacian u) (contDiff_laplacian_of_four u hu) (hasCompactSupport_laplacian u huc) H hH hh x z
  rw [poissonPotential_laplacian hm u (hu.of_le (by norm_num)) huc] at h
  exact h

end OAI.Analysis.PDE.Schauder
