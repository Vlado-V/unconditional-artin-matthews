module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Weak.Elliptic.Regularity
public import OAI.Analysis.PDE.Weak.Elliptic.TestSupport
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
public import OAI.Analysis.PDE.Weak.Elliptic.Divergence


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open Set _root_.MeasureTheory Filter
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem lp_coeFn_finset_sum {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (u : ι → Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))) :
    (⇑(∑ i ∈ s, u i)) =ᵐ[volume] fun x ↦ ∑ i ∈ s, u i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero E 2 volume
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (u i) (∑ j ∈ s, u j), ih] with x hx hy
    simpa only [Finset.sum_insert hi, Pi.add_apply, hy] using hx

theorem weak_negative_divergence_regular
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    (R : Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (G : Fin (m + 1) → Lp (OAI.Analysis.PDE.Variational.CellVectors m) 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)))
    (hG : ∀ i, WeakRegularity Ω k (G i))
    (hder : ∀ i, HasWeakDirectionalDerivativeOn volume Ω (Pi.single i 1) R (G i)) :
    ∃ D : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)),
      WeakRegularity Ω k D ∧ WeakDivergenceEquation Ω R D := by
  let g : Fin (m + 1) → Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)) :=
    fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).compLp (G i)
  let D := -(∑ i, g i)
  have hgreg (i : Fin (m + 1)) : WeakRegularity Ω k (g i) :=
    (hG i).map (EuclideanSpace.proj (𝕜 := ℝ) i)
  have hD : WeakRegularity Ω k D :=
    (OAI.Analysis.PDE.Weak.WeakRegularity.finset_sum Finset.univ g (fun i _ ↦ hgreg i)).neg
  have hproj : ∀ᵐ x ∂volume, ∀ i, g i x = G i x i := by
    apply ae_all_iff.mpr
    intro i
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).coeFn_compLp (G i)
  have hDcoe : (D : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) =ᵐ[volume] fun x ↦ -∑ i, G i x i := by
    filter_upwards [Lp.coeFn_neg (∑ i, g i), lp_coeFn_finset_sum Finset.univ g, hproj]
      with x hx hy hz
    change D x = -(∑ i, g i) x at hx
    rw [hx, hy]
    simp only [hz]
  obtain ⟨-, he⟩ := weak_negative_divergence (Lp.memLp R) (fun i ↦ G i)
    (fun i ↦ Lp.memLp (G i)) hder
  refine ⟨D, hD, ?_⟩
  intro φ hφ hs hsub
  rw [he φ hφ hs hsub]
  apply integral_congr_ae
  filter_upwards [hDcoe] with x hx
  rw [hx]

end OAI.Analysis.PDE.Weak
