module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Weak.Elliptic.H1
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open Set _root_.MeasureTheory
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem smoothH1Pair_zero :
    smoothH1Pair (fun _ : OAI.Analysis.PDE.Variational.CellCoordinates m ↦ (0 : ℝ)) contDiff_const (by simp [HasCompactSupport]) = 0 := by
  apply Prod.ext
  · change (smoothH1Pair _ _ _).1 = (0 : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    apply Lp.ext
    filter_upwards [smoothH1Pair_value_ae (fun _ : OAI.Analysis.PDE.Variational.CellCoordinates m ↦ (0 : ℝ))
      contDiff_const (by simp [HasCompactSupport]), Lp.coeFn_zero (E := ℝ) (p := 2) (μ := (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))]
      with x hx hz
    exact hx.trans hz.symm
  · change (smoothH1Pair _ _ _).2 = (0 : Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    apply Lp.ext
    filter_upwards [smoothH1Pair_gradient_ae (fun _ : OAI.Analysis.PDE.Variational.CellCoordinates m ↦ (0 : ℝ))
      contDiff_const (by simp [HasCompactSupport]), Lp.coeFn_zero (E := OAI.Analysis.PDE.Variational.CellVectors m) (p := 2)
        (μ := (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))] with x hx hz
    rw [hx, hz]
    ext i
    simp [OAI.Analysis.PDE.Variational.cellGradient]

theorem smoothH1Pair_add (u w : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w)
    (hus : HasCompactSupport u) (hws : HasCompactSupport w) :
    smoothH1Pair (u + w) (hu.add hw) (hus.add hws) =
      smoothH1Pair u hu hus + smoothH1Pair w hw hws := by
  apply Prod.ext
  · change (smoothH1Pair _ _ _).1 = (smoothH1Pair u hu hus).1 + (smoothH1Pair w hw hws).1
    apply Lp.ext
    filter_upwards [smoothH1Pair_value_ae (u + w) (hu.add hw) (hus.add hws),
      smoothH1Pair_value_ae u hu hus, smoothH1Pair_value_ae w hw hws,
      Lp.coeFn_add (smoothH1Pair u hu hus).1 (smoothH1Pair w hw hws).1]
      with x hx hy hz ha
    rw [hx, ha]
    simp [hy, hz]
  · change (smoothH1Pair _ _ _).2 = (smoothH1Pair u hu hus).2 + (smoothH1Pair w hw hws).2
    apply Lp.ext
    filter_upwards [smoothH1Pair_gradient_ae (u + w) (hu.add hw) (hus.add hws),
      smoothH1Pair_gradient_ae u hu hus, smoothH1Pair_gradient_ae w hw hws,
      Lp.coeFn_add (smoothH1Pair u hu hus).2 (smoothH1Pair w hw hws).2]
      with x hx hy hz ha
    rw [hx, ha]
    simp only [Pi.add_apply, hy, hz]
    exact congrFun (OAI.Analysis.PDE.Variational.cellGradient_add (hu.differentiable (by simp)) (hw.differentiable (by simp))) x

theorem smoothH1Pair_smul (c : ℝ) (u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    smoothH1Pair (c • u) (hu.const_smul c) hus.smul_left = c • smoothH1Pair u hu hus := by
  apply Prod.ext
  · change (smoothH1Pair _ _ _).1 = c • (smoothH1Pair u hu hus).1
    apply Lp.ext
    filter_upwards [smoothH1Pair_value_ae (c • u) (hu.const_smul c) hus.smul_left,
      smoothH1Pair_value_ae u hu hus, Lp.coeFn_smul c (smoothH1Pair u hu hus).1]
      with x hx hy hz
    rw [hx, hz]
    simp [hy]
  · change (smoothH1Pair _ _ _).2 = c • (smoothH1Pair u hu hus).2
    apply Lp.ext
    filter_upwards [smoothH1Pair_gradient_ae (c • u) (hu.const_smul c) hus.smul_left,
      smoothH1Pair_gradient_ae u hu hus, Lp.coeFn_smul c (smoothH1Pair u hu hus).2]
      with x hx hy hz
    rw [hx, hz]
    simp only [Pi.smul_apply, hy]
    exact congrFun (OAI.Analysis.PDE.Variational.cellGradient_smul c (hu.differentiable (by simp))) x

def smoothH1Submodule (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) : Submodule ℝ (H1Pair m) where
  carrier := smoothH1Graph Ω
  zero_mem' := by
    refine ⟨0, contDiff_const, by simp [HasCompactSupport], by simp, ?_⟩
    exact smoothH1Pair_zero
  add_mem' := by
    rintro p q ⟨u, hu, hus, huΩ, rfl⟩ ⟨w, hw, hws, hwΩ, rfl⟩
    exact ⟨u + w, hu.add hw, hus.add hws,
      (tsupport_add u w).trans (union_subset huΩ hwΩ), smoothH1Pair_add u w hu hw hus hws⟩
  smul_mem' := by
    rintro c p ⟨u, hu, hus, huΩ, rfl⟩
    exact ⟨c • u, hu.const_smul c, hus.smul_left,
      (tsupport_smul_subset_right (fun _ ↦ c) u).trans huΩ, smoothH1Pair_smul c u hu hus⟩

def h1ZeroSubmodule (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) : Submodule ℝ (H1Pair m) :=
  (smoothH1Submodule Ω).topologicalClosure

theorem h1ZeroSubmodule_coe (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) :
    (h1ZeroSubmodule Ω : Set (H1Pair m)) = H1Zero Ω := rfl

abbrev H1Hilbert (m : ℕ) := WithLp 2 (H1Pair m)

def h1HilbertEquiv : H1Hilbert m ≃L[ℝ] H1Pair m :=
  WithLp.prodContinuousLinearEquiv 2 ℝ _ _

def h1ZeroHilbertSubmodule (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) : Submodule ℝ (H1Hilbert m) :=
  (h1ZeroSubmodule Ω).comap h1HilbertEquiv.toLinearMap

theorem isClosed_h1ZeroHilbertSubmodule (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) :
    IsClosed (h1ZeroHilbertSubmodule Ω : Set (H1Hilbert m)) :=
  (smoothH1Submodule Ω).isClosed_topologicalClosure.preimage h1HilbertEquiv.continuous

end OAI.Analysis.PDE.Weak
