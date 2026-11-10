module

public import ArtinMatthews.SpectralGamma0GreenPointSeries
public import ArtinMatthews.SpectralGamma0FiniteGreenPlane
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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


set_option backward.privateInPublic true
@[expose] public section

/-! Actual cuspidal mass vectors representing Green evaluation. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups InnerProductSpace lp
namespace ArtinMatthews

local instance greenEvaluationVector_inner (N : ℕ) [NeZero N] :
    InnerProductSpace ℂ (gamma0AllHeightCuspidalMassSpace N) :=
  Submodule.innerProductSpace (𝕜 := ℂ) (E := Gamma0RegionL2 N) _

def gamma0GreenPointCoordinates (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (p : ℝ × ℝ)
    (hp : 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2) :
    ℓ²(Gamma0AllHeightSpectralIndex N, ℂ) :=
  ⟨fun i => star (gamma0GreenPointCoefficient N r Y hY i p), by
    apply memℓp_gen
    simpa [Real.rpow_two] using gamma0GreenPointCoefficient_square_summable N r Y hY p hp⟩

def gamma0GreenEvaluationVector (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (p : ℝ × ℝ)
    (hp : 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2) : gamma0AllHeightCuspidalMassSpace N :=
  (gamma0FullCuspidalSpectralBasis N).repr.symm (gamma0GreenPointCoordinates N r Y hY p hp)

theorem gamma0GreenEvaluationVector_repr (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (p : ℝ × ℝ)
    (hp : 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2) (i : Gamma0AllHeightSpectralIndex N) :
    (gamma0FullCuspidalSpectralBasis N).repr (gamma0GreenEvaluationVector N r Y hY p hp) i =
      star (gamma0GreenPointCoefficient N r Y hY i p) := by
  unfold gamma0GreenEvaluationVector
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem gamma0GreenEvaluationVector_inner_basis (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (p : ℝ × ℝ)
    (hp : 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2) (i : Gamma0AllHeightSpectralIndex N) :
    inner ℂ (gamma0GreenEvaluationVector N r Y hY p hp) (gamma0FullCuspidalSpectralBasis N i) =
      gamma0GreenPointCoefficient N r Y hY i p := by
  calc
    _ = star (inner ℂ (gamma0FullCuspidalSpectralBasis N i)
        (gamma0GreenEvaluationVector N r Y hY p hp)) :=
      (inner_conj_symm (gamma0GreenEvaluationVector N r Y hY p hp)
        (gamma0FullCuspidalSpectralBasis N i)).symm
    _ = _ := by
      rw [← HilbertBasis.repr_apply_apply,gamma0GreenEvaluationVector_repr]
      exact star_star _

theorem gamma0GreenEvaluationVector_hasSum (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (p : ℝ × ℝ)
    (hp : 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2) :
    HasSum (fun i => star (gamma0GreenPointCoefficient N r Y hY i p) •
      gamma0FullCuspidalSpectralBasis N i) (gamma0GreenEvaluationVector N r Y hY p hp) := by
  exact (gamma0FullCuspidalSpectralBasis N).hasSum_repr_symm
    (gamma0GreenPointCoordinates N r Y hY p hp)

theorem gamma0GreenSquaredPointKernel_eq_inner (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (p q : ℝ × ℝ)
    (hp : 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2)
    (hq : 0 < q.1 ∧ q.1 < 2*(N:ℝ) ∧ Y < q.2) :
    gamma0GreenSquaredPointKernel N r Y hY p q =
      inner ℂ (gamma0GreenEvaluationVector N r Y hY p hp)
        (gamma0GreenEvaluationVector N r Y hY q hq) := by
  unfold gamma0GreenSquaredPointKernel
  have h := (gamma0FullCuspidalSpectralBasis N).hasSum_inner_mul_inner
    (gamma0GreenEvaluationVector N r Y hY p hp) (gamma0GreenEvaluationVector N r Y hY q hq)
  simpa only [gamma0GreenEvaluationVector_inner_basis,← HilbertBasis.repr_apply_apply,
    gamma0GreenEvaluationVector_repr] using h.tsum_eq

theorem gamma0GreenEvaluationVector_compact_bound (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKΩ : K ⊆ {p | 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2}) :
    ∃ C : ℝ, 0 < C ∧ ∀ p (hp : p ∈ K),
      ‖gamma0GreenEvaluationVector N r Y hY p (hKΩ hp)‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := gamma0GreenPointCoefficient_square_compact_bound N r Y hY hK hKΩ
  refine ⟨C,hC,?_⟩
  intro p hp
  unfold gamma0GreenEvaluationVector
  rw [LinearIsometryEquiv.norm_map]
  apply lp.norm_le_of_tsum_le (by norm_num : 0 < (2 : ENNReal).toReal) hC.le
  simpa [gamma0GreenPointCoordinates,Real.rpow_two] using (hb p hp).2

theorem gamma0GreenEvaluationVector_finiteGreenPlane (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) (p : ℝ × ℝ)
    (hp : 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2)
    (s : Finset (Gamma0AllHeightSpectralIndex N)) (c : Gamma0AllHeightSpectralIndex N → ℝ) :
    inner ℂ (gamma0GreenEvaluationVector N r Y hY p hp).val (gamma0FiniteMassCombination N s c) =
      gamma0FiniteGreenPlane N r Y hY s c p := by
  unfold gamma0FiniteMassCombination gamma0FiniteGreenPlane
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_smul_right]
  have he : inner ℂ (gamma0GreenEvaluationVector N r Y hY p hp).val
      (gamma0FullCuspidalSpectralBasis N i).val = gamma0GreenPointCoefficient N r Y hY i p :=
    gamma0GreenEvaluationVector_inner_basis N r Y hY p hp i
  rw [he]
  simp only [gamma0GreenPointCoefficient,Complex.real_smul]
  push_cast
  ring

end ArtinMatthews
