module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Variational.LocalEquation
public import OAI.Analysis.PDE.Variational.LocalH1
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

open Set Filter _root_.MeasureTheory
open scoped ContDiff Topology
noncomputable section

namespace OAI.Analysis.PDE.Variational

open OAI.Analysis.PDE.Weak

variable {m : ℕ}

theorem weakEquation_congr_on {Ω Ω' : Set (CellCoordinates m)}
    {H H' : CellCoordinates m → CellVectors m} {f f' : CellCoordinates m → ℝ}
    (hweak : OAI.Analysis.PDE.Weak.WeakDivergenceEquation Ω H f) (hsub : Ω'⊆Ω)
    (hH : ∀ᵐ x ∂volume, x∈Ω' → H' x=H x)
    (hf : ∀ᵐ x ∂volume, x∈Ω' → f' x=f x) :
    OAI.Analysis.PDE.Weak.WeakDivergenceEquation Ω' H' f' := by
  intro φ hφ hc hs
  calc
    _ = ∫ x, inner ℝ (H x) (cellGradient φ x) := by
      apply integral_congr_ae
      filter_upwards [hH] with x hx
      by_cases hxo : x∈Ω'
      · rw [hx hxo]
      · have ht : x∉tsupport φ := fun ht ↦ hxo (hs ht)
        rw [cellGradient_zero_off_tsupport ht]
        simp
    _ = ∫ x, f x * φ x := hweak φ hφ hc (hs.trans hsub)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      by_cases hxo : x∈Ω'
      · rw [hx hxo]
      · have hzero : φ x=0 := by
          by_contra hne
          exact hxo (hs (subset_tsupport _ hne))
        simp only [hzero, mul_zero]

theorem cellGradient_eq_zero_of_eq_one {Ω : Set (CellCoordinates m)} (hΩ : IsOpen Ω)
    {η : CellCoordinates m → ℝ} (hη : ∀ x∈Ω, η x=1)
    {x : CellCoordinates m} (hx : x∈Ω) : cellGradient η x=0 := by
  have heq : η =ᶠ[𝓝 x] (fun _ ↦ (1:ℝ)) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact hη y hy
  ext i
  simp only [cellGradient_apply, heq.fderiv_eq, WithLp.ofLp_zero, Pi.zero_apply]
  exact congrArg (fun L : CellCoordinates m →L[ℝ] ℝ ↦ L (Pi.single i 1))
    (hasFDerivAt_const (c := (1:ℝ)) x).fderiv

theorem cutoffH1Pair_eq_on (Ω : Set (CellCoordinates m)) (hΩ : IsOpen Ω)
    (η : CellCoordinates m → ℝ) (hη : ContDiff ℝ 1 η)
    {M K : ℝ} (hM : ∀ x, |η x|≤M) (hK : ∀ x, ‖cellGradient η x‖≤K)
    (hone : ∀ x∈Ω, η x=1) (p : OAI.Analysis.PDE.Weak.H1Pair m) :
    ∀ᵐ x ∂volume, x∈Ω →
      (OAI.Analysis.PDE.Weak.cutoffH1Pair η hη hM hK p).1 x=p.1 x ∧
      (OAI.Analysis.PDE.Weak.cutoffH1Pair η hη hM hK p).2 x=p.2 x := by
  filter_upwards [OAI.Analysis.PDE.Weak.cutoffH1Pair_value_ae η hη hM hK p,
    OAI.Analysis.PDE.Weak.cutoffH1Pair_gradient_ae η hη hM hK p] with x hv hg
  intro hx
  rw [hv, hg, hone x hx, cellGradient_eq_zero_of_eq_one hΩ hone hx]
  simp

theorem weakEquation_cutoff {Ω Ω' : Set (CellCoordinates m)} (hΩ' : IsOpen Ω')
    (hsub : Ω'⊆Ω) (p : OAI.Analysis.PDE.Weak.H1Pair m)
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (f : CellCoordinates m → ℝ)
    (hweak : OAI.Analysis.PDE.Weak.WeakDivergenceEquation Ω (fun x ↦ A x (p.2 x)) f)
    (η : CellCoordinates m → ℝ) (hη : ContDiff ℝ 1 η)
    {M K : ℝ} (hM : ∀ x, |η x|≤M) (hK : ∀ x, ‖cellGradient η x‖≤K)
    (hone : ∀ x∈Ω', η x=1) :
    OAI.Analysis.PDE.Weak.WeakDivergenceEquation Ω'
      (fun x ↦ A x ((OAI.Analysis.PDE.Weak.cutoffH1Pair η hη hM hK p).2 x)) f := by
  apply weakEquation_congr_on hweak hsub
  · filter_upwards [cutoffH1Pair_eq_on Ω' hΩ' η hη hM hK hone p] with x hx
    intro hxo
    rw [(hx hxo).2]
  · exact Filter.Eventually.of_forall fun _ _ ↦ rfl

theorem periodicH1Pair_equation {a b : CellCoordinates m} {Ω P : Set (CellCoordinates m)}
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    {M : ℝ} (hM : 0≤M) (hAM : ∀ᵐ x ∂volume.restrict (Icc a b), ‖A x‖≤M)
    (u : PeriodicH10 a b Ω P) (f : CellCoordinates m → ℝ)
    (hweak : OAI.Analysis.PDE.Weak.WeakDivergenceEquation (Ω∩cellInterior a b)
      (coefficientCellFlux a b Ω P A hA hM hAM u) f) :
    OAI.Analysis.PDE.Weak.WeakDivergenceEquation (Ω∩cellInterior a b)
      (fun x ↦ A x ((periodicH1Pair a b Ω P u).2 x)) f := by
  apply weakEquation_congr_on hweak Subset.rfl
  · filter_upwards [periodicH1Pair_gradient_ae a b Ω P u,
      coefficientCellFlux_ae a b Ω P A hA hM hAM u] with x hx hy
    intro _
    rw [hx, hy]
  · exact Filter.Eventually.of_forall fun _ _ ↦ rfl

end OAI.Analysis.PDE.Variational
