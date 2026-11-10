module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Weak.Elliptic.Cutoff
public import OAI.Analysis.PDE.Weak.Elliptic.Derivative
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


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
namespace OAI.Analysis.PDE.Weak

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (μ : Measure X)

def HasWeakDirectionalDerivativeOn (Ω : Set X) (v : X) (u g : X → E) : Prop :=
  ∀ φ : X → E, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    (∫ x, inner ℝ (g x) (φ x) ∂μ) = -(∫ x, inner ℝ (u x) (fderiv ℝ φ x v) ∂μ)

omit [BorelSpace X] [SecondCountableTopology X] in
theorem HasWeakDirectionalDerivativeOn.congr_on
    {Ω : Set X} {v : X} {u g u' g' : X → E}
    (hg : HasWeakDirectionalDerivativeOn μ Ω v u g)
    (hu : ∀ᵐ x ∂μ, x ∈ Ω → u x = u' x)
    (hh : ∀ᵐ x ∂μ, x ∈ Ω → g x = g' x) :
    HasWeakDirectionalDerivativeOn μ Ω v u' g' := by
  intro φ hφ hs hsub
  have hl : (∫ x, inner ℝ (g x) (φ x) ∂μ) = ∫ x, inner ℝ (g' x) (φ x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hh] with x hx
    by_cases hxs : x ∈ tsupport φ
    · rw [hx (hsub hxs)]
    · simp [image_eq_zero_of_notMem_tsupport hxs]
  have hr : (∫ x, inner ℝ (u x) (fderiv ℝ φ x v) ∂μ) =
      ∫ x, inner ℝ (u' x) (fderiv ℝ φ x v) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hu] with x hx
    by_cases hxs : x ∈ tsupport φ
    · rw [hx (hsub hxs)]
    · have hd : fderiv ℝ φ x = 0 := by
        by_contra hd
        exact hxs ((support_fderiv_subset ℝ) hd)
      simp [hd]
  rw [← hl, ← hr]
  exact hg φ hφ hs hsub

omit [BorelSpace X] [SecondCountableTopology X] in
theorem HasWeakDirectionalDerivativeOn.mono {Ω Ω' : Set X} {v : X} {u g : X → E}
    (hg : HasWeakDirectionalDerivativeOn μ Ω v u g) (hsub : Ω' ⊆ Ω) :
    HasWeakDirectionalDerivativeOn μ Ω' v u g :=
  fun φ hφ hs hφsub ↦ hg φ hφ hs (hφsub.trans hsub)

variable [CompleteSpace E] [μ.IsAddRightInvariant] [IsLocallyFiniteMeasure μ]

omit [BorelSpace X] [SecondCountableTopology X] [CompleteSpace E] [μ.IsAddRightInvariant] [IsLocallyFiniteMeasure μ] in
theorem HasWeakDirectionalDerivative.on
    {Ω : Set X} {v : X} {u g : X → E}
    (hg : HasWeakDirectionalDerivative μ v u g) :
    HasWeakDirectionalDerivativeOn μ Ω v u g :=
  fun φ hφ hs _ ↦ hg φ hφ hs

omit [CompleteSpace E] [μ.IsAddRightInvariant] [IsLocallyFiniteMeasure μ] in
/-- A derivative of the localized field is the actual local derivative
on every region where its cutoff is one. -/
theorem HasWeakDirectionalDerivative.cutoff_eq_one
    {Ω : Set X} {η : X → ℝ} (hη : Continuous η) {M : ℝ}
    (hM : ∀ x, |η x| ≤ M) (hone : ∀ x ∈ Ω, η x = 1)
    {v : X} {u : Lp E 2 μ} {g : X → E}
    (hg : HasWeakDirectionalDerivative μ v (cutoffL2 η hη hM u) g) :
    HasWeakDirectionalDerivativeOn μ Ω v u g := by
  intro φ hφ hs hsub
  rw [hg φ hφ hs]
  congr 1
  apply integral_congr_ae
  filter_upwards [cutoffL2_ae η hη hM u] with x hx
  by_cases hxs : x ∈ tsupport φ
  · rw [hx, hone x (hsub hxs), one_smul]
  · have hd : fderiv ℝ φ x = 0 := by
      by_contra hd
      exact hxs ((support_fderiv_subset ℝ) hd)
    simp [hd]

end OAI.Analysis.PDE.Weak
