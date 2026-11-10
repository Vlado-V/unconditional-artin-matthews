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
public import OAI.Analysis.PDE.Weak.Boundary.H1WeakGradient


set_option backward.privateInPublic true
@[expose] public section

open Set _root_.MeasureTheory InnerProductSpace
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Variational

open OAI.Analysis.PDE.Weak

variable {m : ℕ}

def cellDivergence (B : CellCoordinates m → CellVectors m) (x : CellCoordinates m) : ℝ :=
  ∑ j, fderiv ℝ (fun y ↦ B y j) x (Pi.single j 1)

theorem contDiff_cell_component {n : WithTop ℕ∞} {B : CellCoordinates m → CellVectors m}
    (hB : ContDiff ℝ n B) (j : Fin (m+1)) : ContDiff ℝ n (fun x ↦ B x j) := by
  exact (EuclideanSpace.proj j).contDiff.comp hB

theorem continuous_cellDivergence {B : CellCoordinates m → CellVectors m}
    (hB : ContDiff ℝ 1 B) : Continuous (cellDivergence B) := by
  apply continuous_finsetSum
  intro j _
  exact ((contDiff_cell_component hB j).continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem hasCompactSupport_cellDivergence {B : CellCoordinates m → CellVectors m}
    (hB : HasCompactSupport B) : HasCompactSupport (cellDivergence B) := by
  classical
  have hterm j : HasCompactSupport (fun x ↦ fderiv ℝ (fun y ↦ B y j) x (Pi.single j 1)) := by
    have hs : HasCompactSupport (fun x ↦ B x j) :=
      hB.comp_left (g := fun v : CellVectors m ↦ v j) (by simp)
    exact hs.fderiv_apply ℝ _
  have hfin (s : Finset (Fin (m+1))) :
      HasCompactSupport (fun x ↦ ∑ j∈s, fderiv ℝ (fun y ↦ B y j) x (Pi.single j 1)) := by
    induction s using Finset.induction_on with
    | empty => simp [HasCompactSupport]
    | @insert j s hj ih =>
      convert (hterm j).add ih using 1
      ext x
      simp only [Finset.sum_insert hj, Pi.add_apply]
  exact hfin Finset.univ

/-- Integration by parts for the actual H¹ graph and a compact C¹ vector field. -/
theorem H1Zero.integral_divergence {Ω : Set (CellCoordinates m)} {p : OAI.Analysis.PDE.Weak.H1Pair m}
    (hp : p∈OAI.Analysis.PDE.Weak.H1Zero Ω) (B : CellCoordinates m → CellVectors m)
    (hB : ContDiff ℝ 1 B) (hs : HasCompactSupport B) :
    (∫ x, inner ℝ (p.2 x) (B x)) = -(∫ x, p.1 x * cellDivergence B x) := by
  have hc j : ContDiff ℝ 1 (fun x ↦ B x j) := contDiff_cell_component hB j
  have hcs j : HasCompactSupport (fun x ↦ B x j) :=
    hs.comp_left (g := fun v : CellVectors m ↦ v j) (by simp)
  have hc2 j : MemLp (fun x ↦ B x j) 2 volume := (hc j).continuous.memLp_of_hasCompactSupport (hcs j)
  have hd2 j : MemLp (fun x ↦ fderiv ℝ (fun y ↦ B y j) x (Pi.single j 1)) 2 volume :=
    (((hc j).continuous_fderiv one_ne_zero).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hcs j).fderiv_apply ℝ _)
  have hp2 j : MemLp (fun x ↦ p.2 x j) 2 volume := by
    exact (EuclideanSpace.proj (𝕜:=ℝ) j).comp_memLp p.2
  have he j := OAI.Analysis.PDE.Weak.H1Zero.weak_derivative hp j (fun x ↦ B x j) (hc j) (hcs j)
  have hi x : inner ℝ (p.2 x) (B x) = ∑ j, p.2 x j * B x j := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hi, cellDivergence, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (f:=fun j x ↦ p.2 x j*B x j)
      (fun j _ ↦ (hp2 j).integrable_mul (hc2 j)),
    integral_finsetSum Finset.univ (f:=fun j x ↦ p.1 x*fderiv ℝ (fun y ↦ B y j) x (Pi.single j 1))
      (fun j _ ↦ (Lp.memLp p.1).integrable_mul (hd2 j)),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun j _ ↦ he j)

theorem cellDivergence_smul {B : CellCoordinates m → CellVectors m}
    {φ : CellCoordinates m → ℝ} (hB : Differentiable ℝ B) (hφ : Differentiable ℝ φ) (x) :
    cellDivergence (fun y ↦ φ y • B y) x =
      inner ℝ (B x) (cellGradient φ x) + φ x * cellDivergence B x := by
  have hc j : Differentiable ℝ (fun y ↦ B y j) :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).differentiable.comp hB
  have hd j : fderiv ℝ (fun y ↦ (φ y • B y) j) x (Pi.single j 1) =
      fderiv ℝ φ x (Pi.single j 1)*B x j + φ x*fderiv ℝ (fun y ↦ B y j) x (Pi.single j 1) := by
    change fderiv ℝ (φ * fun y ↦ B y j) x _ = _
    rw [((hφ x).hasFDerivAt.mul (hc j x).hasFDerivAt).fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  simp only [cellDivergence, hd, Finset.sum_add_distrib, Finset.mul_sum,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, cellGradient_apply]

end OAI.Analysis.PDE.Variational
