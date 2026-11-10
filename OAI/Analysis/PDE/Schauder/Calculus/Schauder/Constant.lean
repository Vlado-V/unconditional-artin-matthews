module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Linear
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Perturbation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Compact


set_option backward.privateInPublic true
@[expose] public section

/-! Sharp Schauder estimates for every elliptic constant matrix given by its real factor. -/

noncomputable section
open _root_.MeasureTheory Set Metric InnerProductSpace Laplacian
namespace OAI.Analysis.PDE.Schauder

theorem compact_constant_coefficient_schauder {m : ℕ} (hm : 3 ≤ m)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)) :
    ∃ C > 0, ∀ (u : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
      ∀ F, 0 ≤ F →
      (∀ x y, |nondivergenceOperator (fun _ => linearEllipticMatrix L.toContinuousLinearMap) u x -
        nondivergenceOperator (fun _ => linearEllipticMatrix L.toContinuousLinearMap) u y| ≤ F * ‖x - y‖ ^ α) →
      ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ C * F * ‖x - y‖ ^ α := by
  obtain ⟨S, hS, hs⟩ := compact_schauder_estimate_C2 hm hα hα1
  let a : ℝ := ‖L.toContinuousLinearMap‖ ^ α
  let b : ℝ := ‖L.symm.toContinuousLinearMap‖ ^ α
  let c : ℝ := ‖L.symm.toContinuousLinearMap‖ ^ 2
  have ha : 0 ≤ a := Real.rpow_nonneg (norm_nonneg _) _
  have hb : 0 ≤ b := Real.rpow_nonneg (norm_nonneg _) _
  have hc : 0 ≤ c := sq_nonneg _
  refine ⟨S * a * b * c + 1, by positivity, ?_⟩
  intro u hu huc F hF hforce x y
  let g := u ∘ L.toContinuousLinearMap
  have hg : ContDiff ℝ 2 g := hu.comp L.contDiff
  have hgc : HasCompactSupport g := huc.comp_homeomorph L.toHomeomorph
  have hlap : laplacian g = fun z => nondivergenceOperator (fun _ => linearEllipticMatrix L.toContinuousLinearMap) u (L z) := by
    funext z
    unfold nondivergenceOperator
    exact laplacian_comp_linear u hu L.toContinuousLinearMap z
  have hgf (z w : EuclideanSpace ℝ (Fin m)) : |laplacian g z - laplacian g w| ≤ (F * a) * ‖z - w‖ ^ α := by
    rw [hlap]
    have hnorm : ‖L z - L w‖ ≤ ‖L.toContinuousLinearMap‖ * ‖z - w‖ := by
      simpa only [map_sub] using! L.toContinuousLinearMap.le_opNorm (z - w)
    calc
      _ ≤ F * ‖L z - L w‖ ^ α := hforce _ _
      _ ≤ F * (‖L.toContinuousLinearMap‖ * ‖z - w‖) ^ α :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hnorm hα.le) hF
      _ = _ := by rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]; dsimp [a]; ring
  have hnorm : ‖L.symm x - L.symm y‖ ≤ ‖L.symm.toContinuousLinearMap‖ * ‖x - y‖ := by
    simpa only [map_sub] using! L.symm.toContinuousLinearMap.le_opNorm (x - y)
  have hdiff := hs g hg hgc (F * a) (mul_nonneg hF ha) hgf (L.symm y) (L.symm x)
  have hpull : ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
      ‖fderiv ℝ (fderiv ℝ g) (L.symm x) - fderiv ℝ (fderiv ℝ g) (L.symm y)‖ * c := by
    apply bilinear_norm_le_pullback _ _ L.symm.toContinuousLinearMap
    intro v w
    change fderiv ℝ (fderiv ℝ u) x v w - fderiv ℝ (fderiv ℝ u) y v w =
      fderiv ℝ (fderiv ℝ g) (L.symm x) (L.symm v) (L.symm w) -
      fderiv ℝ (fderiv ℝ g) (L.symm y) (L.symm v) (L.symm w)
    dsimp only [g]
    rw [second_fderiv_comp_linear u hu, second_fderiv_comp_linear u hu]
    simp
  calc
    _ ≤ (S * (F * a) * ‖L.symm x - L.symm y‖ ^ α) * c :=
      hpull.trans (mul_le_mul_of_nonneg_right hdiff hc)
    _ ≤ (S * (F * a) * (‖L.symm.toContinuousLinearMap‖ * ‖x - y‖) ^ α) * c := by
      gcongr
    _ = (S * a * b * c) * F * ‖x - y‖ ^ α := by
      rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
      dsimp [b]
      ring
    _ ≤ (S * a * b * c + 1) * F * ‖x - y‖ ^ α := by gcongr; linarith

end OAI.Analysis.PDE.Schauder
