module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Echelon.Zsqrtd


set_option backward.privateInPublic true
@[expose] public section

/-! Completion of actual test gradients.  The scalar-value map is constructed
by extending the Poincaré-controlled test-value map. -/

open Set
noncomputable section

namespace OAI.Analysis.PDE.Variational

variable {T H Y : Type*} [AddCommGroup T] [Module ℝ T]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

abbrev GradientCompletion (g : T →ₗ[ℝ] H) := ↥g.range.topologicalClosure

def testGradient (g : T →ₗ[ℝ] H) : T →ₗ[ℝ] GradientCompletion g :=
  g.codRestrict g.range.topologicalClosure
    (fun t ↦ g.range.le_topologicalClosure (LinearMap.mem_range_self g t))

@[simp] theorem coe_testGradient (g : T →ₗ[ℝ] H) (t : T) :
    (testGradient g t : H) = g t := rfl

theorem denseRange_testGradient (g : T →ₗ[ℝ] H) : DenseRange (testGradient g) := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  have hx : (x : H) ∈ closure (Set.range g) := x.property
  obtain ⟨y, ⟨t, rfl⟩, ht⟩ := Metric.mem_closure_iff.mp hx ε hε
  exact ⟨t, ht⟩

def completedValue (g : T →ₗ[ℝ] H) (v : T →ₗ[ℝ] Y) :
    GradientCompletion g →L[ℝ] Y := v.extendOfNorm (testGradient g)

theorem completedValue_testGradient (g : T →ₗ[ℝ] H) (v : T →ₗ[ℝ] Y)
    {C : ℝ} (hC : ∀ t, ‖v t‖ ≤ C * ‖g t‖) (t : T) :
    completedValue g v (testGradient g t) = v t :=
  LinearMap.extendOfNorm_eq (denseRange_testGradient g) ⟨C, hC⟩ t

theorem norm_completedValue_le (g : T →ₗ[ℝ] H) (v : T →ₗ[ℝ] Y)
    {C : ℝ} (hC : ∀ t, ‖v t‖ ≤ C * ‖g t‖) (u : GradientCompletion g) :
    ‖completedValue g v u‖ ≤ C * ‖u‖ :=
  LinearMap.norm_extendOfNorm_apply_le (denseRange_testGradient g) C hC u

/-- Every continuous integration-by-parts identity on the genuine tests passes
to the completed scalar values and gradient fields. -/
theorem completedValue_pairing (g : T →ₗ[ℝ] H) (v : T →ₗ[ℝ] Y)
    {C : ℝ} (hC : ∀ t, ‖v t‖ ≤ C * ‖g t‖)
    (A : Y →L[ℝ] ℝ) (B : H →L[ℝ] ℝ)
    (h : ∀ t, A (v t) = B (g t)) (u : GradientCompletion g) :
    A (completedValue g v u) = B (u : H) := by
  have heq := (denseRange_testGradient g).equalizer
    (A.continuous.comp (completedValue g v).continuous)
    (B.continuous.comp continuous_subtype_val)
    (funext fun t ↦ by
      simpa only [Function.comp_apply, completedValue_testGradient g v hC, coe_testGradient] using h t)
  exact congrFun heq u

end OAI.Analysis.PDE.Variational
