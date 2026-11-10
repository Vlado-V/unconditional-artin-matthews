module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Weak.Elliptic.LocalDerivative
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
public import OAI.Analysis.PDE.Dirichlet.Derivative
public import OAI.Analysis.PDE.Variational.WeakGradient
public import OAI.Analysis.PDE.Weak.Boundary.H1WeakGradient


set_option backward.privateInPublic true
@[expose] public section

/-! Componentwise distributional derivatives and symmetry of mixed
derivatives of the actual H¹ gradient. -/

noncomputable section
open Set Filter _root_.MeasureTheory InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem HasWeakDirectionalDerivativeOn.component
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {v : OAI.Analysis.PDE.Variational.CellCoordinates m}
    {u g : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m}
    (hd : HasWeakDirectionalDerivativeOn volume Ω v u g)
    (j : Fin (m + 1)) (φ : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) (hΩ : tsupport φ ⊆ Ω) :
    (∫ x, g x j * φ x) = -(∫ x, u x j * fderiv ℝ φ x v) := by
  have ht : ContDiff ℝ 1 (OAI.Analysis.PDE.Variational.coordinateTestVector j φ) := hφ.smul contDiff_const
  have hts : HasCompactSupport (OAI.Analysis.PDE.Variational.coordinateTestVector j φ) := by
    change HasCompactSupport ((fun t : ℝ => t • EuclideanSpace.single j (1 : ℝ)) ∘ φ)
    apply hs.comp_left
    simp
  have hsub : tsupport (OAI.Analysis.PDE.Variational.coordinateTestVector j φ) ⊆ Ω := by
    apply Subset.trans (b := tsupport φ) _ hΩ
    change tsupport (fun x => φ x • EuclideanSpace.single j (1 : ℝ)) ⊆ tsupport φ
    apply closure_minimal _ (isClosed_tsupport φ)
    intro x hx
    by_contra hnot
    have hz := image_eq_zero_of_notMem_tsupport hnot
    exact hx (by simp only [hz, zero_smul])
  have he := hd (OAI.Analysis.PDE.Variational.coordinateTestVector j φ) ht hts hsub
  have hf (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
      fderiv ℝ (OAI.Analysis.PDE.Variational.coordinateTestVector j φ) x v =
        OAI.Analysis.PDE.Variational.coordinateTestVector j (fun x => fderiv ℝ φ x v) x := by
    have h := ((hφ.differentiable (by norm_num) x).hasFDerivAt.smul_const
      (EuclideanSpace.single j (1 : ℝ))).fderiv
    exact congrArg (fun L => L v) h
  have hi (w : OAI.Analysis.PDE.Variational.CellVectors m) (ψ : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
      inner ℝ w (OAI.Analysis.PDE.Variational.coordinateTestVector j ψ x) = w j * ψ x := by
    rw [real_inner_comm, OAI.Analysis.PDE.Variational.inner_coordinateTestVector, mul_comm]
  simpa only [hf, hi] using he

theorem H1Zero.mixed_weak_pairing {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {p : H1Pair m}
    (hp : p ∈ H1Zero Ω) (i j : Fin (m + 1))
    (φ : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    (∫ x, p.2 x j * fderiv ℝ φ x (Pi.single i 1)) =
      ∫ x, p.2 x i * fderiv ℝ φ x (Pi.single j 1) := by
  have hi : ContDiff ℝ 1 (fun x => fderiv ℝ φ x (Pi.single i 1)) :=
    OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hφ (by norm_num) _
  have hj : ContDiff ℝ 1 (fun x => fderiv ℝ φ x (Pi.single j 1)) :=
    OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hφ (by norm_num) _
  rw [OAI.Analysis.PDE.Weak.H1Zero.weak_derivative hp j _ hi (hs.fderiv_apply ℝ _),
    OAI.Analysis.PDE.Weak.H1Zero.weak_derivative hp i _ hj (hs.fderiv_apply ℝ _)]
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  exact congrArg (fun t => p.1 x * t)
    (OAI.Analysis.PDE.Dirichlet.directionalDerivative_comm hφ (Pi.single j 1) (Pi.single i 1) x)

end OAI.Analysis.PDE.Weak
