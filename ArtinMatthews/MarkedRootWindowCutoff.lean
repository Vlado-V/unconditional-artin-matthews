module

public import ArtinMatthews.MarkedRootStateWindow
public import ArtinMatthews.MarkedRawStateInclude
public import ArtinMatthews.MarkedRootMemoryEndpointTest
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The actual physical root endpoint test is the zero extension of the
literal full first/beta-good cutoff on its finite box window. The chosen
primitive completions and every active and pending coordinate agree. -/

noncomputable section
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (e : J → ℝ) (x d₀ Y U V : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)

include hZ in
theorem markedRootStateWindow_primitive (p : ℝ × (ℝ × ℝ)) :
    ∀ z∈markedRootStateWindow Z U V p,IsCoprime z.1 z.2 :=
  fun z hz => hZ z (markedRootStateWindow_subset Z U V p hz)

theorem markedRootMemoryEndpointTest_eq_zero_of_outside (p : ℝ × (ℝ × ℝ))
    (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z)
    (hs : s.1.1∉markedRootStateWindow Z U V p) :
    markedRootMemoryEndpointTest e x d₀ Y U V hZ p s=0 := by
  have hb : ¬MarkedRootPhysicalBox U V (markedRootIntegerVector s.1.1) p :=
    fun hb => hs (Finset.mem_filter.mpr ⟨s.1.2,hb⟩)
  simp only [markedRootMemoryEndpointTest,MarkedRootMemoryEndpointGood,hb,false_and,and_false,ite_false]

set_option backward.isDefEq.respectTransparency false in
theorem markedRootMemoryEndpointTest_window (p : ℝ × (ℝ × ℝ))
    (hp : p∈markedRootBoxDomain)
    (s : MarkedRawState (markedRawActualPrimeBand e x) M B (markedRootStateWindow Z U V p)) :
    markedRootMemoryEndpointTest e x d₀ Y U V hZ p
      (markedRawStateInclude (markedRootStateWindow_subset Z U V p) s)=
      markedRawDirtyGoodCutoff e x p.1 d₀ Y
        (fun z => markedPrimitiveCoordinateCompletion z.1
          (markedRootStateWindow_primitive U V hZ p _ z.2)) (fun _ => 1) s := by
  have hb := (Finset.mem_filter.mp s.1.2).2
  rw [markedRawDirtyGoodCutoff_eq_ite]
  unfold markedRootMemoryEndpointTest MarkedRootMemoryEndpointGood markedRawStateInclude
  simp only [hp,hb,true_and]
  rfl

end ArtinMatthews
