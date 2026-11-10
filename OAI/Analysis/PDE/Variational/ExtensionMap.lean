module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Variational.ZeroExtension
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

open Set Filter _root_.MeasureTheory
noncomputable section

namespace OAI.Analysis.PDE.Variational

variable {m : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [NormedSpace ℝ H] in
theorem cellZeroExtension_add (a b : CellCoordinates m)
    (f g : Lp H 2 (volume.restrict (Icc a b))) :
    cellZeroExtension a b (f+g) =ᵐ[volume] cellZeroExtension a b f + cellZeroExtension a b g := by
  have h := (ae_restrict_iff' measurableSet_Icc).mp (Lp.coeFn_add f g)
  filter_upwards [h] with x hx
  by_cases hxc : x∈Icc a b
  · simpa [cellZeroExtension, hxc] using hx hxc
  · simp [cellZeroExtension, hxc]

theorem cellZeroExtension_smul (a b : CellCoordinates m) (c : ℝ)
    (f : Lp H 2 (volume.restrict (Icc a b))) :
    cellZeroExtension a b (c • f) =ᵐ[volume] c • cellZeroExtension a b f := by
  have h := (ae_restrict_iff' measurableSet_Icc).mp (Lp.coeFn_smul c f)
  filter_upwards [h] with x hx
  by_cases hxc : x∈Icc a b
  · simpa [cellZeroExtension, hxc] using hx hxc
  · simp [cellZeroExtension, hxc]

def cellZeroExtensionLinear (a b : CellCoordinates m) :
    Lp H 2 (volume.restrict (Icc a b)) →ₗ[ℝ] Lp H 2 (volume : Measure (CellCoordinates m)) where
  toFun f := (memLp_cellZeroExtension a b f).toLp (cellZeroExtension a b f)
  map_add' f g := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (cellZeroExtension_add a b f g)
  map_smul' c f := by
    change _ = c • (memLp_cellZeroExtension a b f).toLp _
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (cellZeroExtension_smul a b c f)

theorem norm_cellZeroExtensionLinear (a b : CellCoordinates m)
    (f : Lp H 2 (volume.restrict (Icc a b))) : ‖cellZeroExtensionLinear a b f‖ = ‖f‖ := by
  change ‖(memLp_cellZeroExtension a b f).toLp (cellZeroExtension a b f)‖ = ‖f‖
  rw [Lp.norm_toLp, cellZeroExtension, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc.nullMeasurableSet,
    Lp.norm_def]

def cellZeroExtensionL2 (a b : CellCoordinates m) :
    Lp H 2 (volume.restrict (Icc a b)) →L[ℝ] Lp H 2 (volume : Measure (CellCoordinates m)) :=
  (cellZeroExtensionLinear a b).mkContinuous 1 (fun f ↦ by
    rw [norm_cellZeroExtensionLinear, one_mul])

theorem cellZeroExtensionL2_ae (a b : CellCoordinates m)
    (f : Lp H 2 (volume.restrict (Icc a b))) :
    cellZeroExtensionL2 a b f =ᵐ[volume] cellZeroExtension a b f :=
  (memLp_cellZeroExtension a b f).coeFn_toLp

end OAI.Analysis.PDE.Variational
