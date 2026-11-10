module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Polynomial.Basic
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

namespace OAI.Analysis.Calculus.Quaternion

noncomputable section

section Trilinear
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Cubic polarization, without any symmetry assumption on the trilinear form. -/
theorem trilinear_six_term (B : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] W)
    (hB : ∀ x, B x x x = 0) (x y z : V) :
    B x y z + B x z y + B y x z + B y z x + B z x y + B z y x = 0 := by
  have hpoly :
      B x y z + B x z y + B y x z + B y z x + B z x y + B z y x =
      B (x + y + z) (x + y + z) (x + y + z) - B (x + y) (x + y) (x + y) -
        B (x + z) (x + z) (x + z) - B (y + z) (y + z) (y + z) +
        B x x x + B y y y + B z z z := by
    simp only [map_add, LinearMap.add_apply]
    abel
  simpa only [hB, sub_zero, add_zero] using hpoly

end Trilinear

section Contraction
variable {ι W : Type*} [Fintype ι] [AddCommGroup W] [Module ℝ W]

def cubicContraction (T : ι → ι → ι → ℝ) (C : ι → ι → ι → W) : W :=
  ∑ i, ∑ j, ∑ k, T i j k • C i j k

theorem cubicContraction_swap12 (T : ι → ι → ι → ℝ)
    (hT : ∀ i j k, T i j k = T j i k) (C : ι → ι → ι → W) :
    cubicContraction T (fun i j k => C j i k) = cubicContraction T C := by
  unfold cubicContraction
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [hT j i k]

theorem cubicContraction_swap23 (T : ι → ι → ι → ℝ)
    (hT : ∀ i j k, T i j k = T i k j) (C : ι → ι → ι → W) :
    cubicContraction T (fun i j k => C i k j) = cubicContraction T C := by
  unfold cubicContraction
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [hT i k j]

/-- A cubic symbol vanishing on every diagonal annihilates every symmetric
third-order tensor. This is the algebraic passage from symbols to the
third derivatives in the cofactor-divergence identity. -/
theorem trilinear_symmetric_contraction_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] W) (hB : ∀ x, B x x x = 0)
    (e : ι → V) (T : ι → ι → ι → ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j) :
    cubicContraction T (fun i j k => B (e i) (e j) (e k)) = 0 := by
  let C := fun i j k => B (e i) (e j) (e k)
  have hz : cubicContraction T (fun i j k =>
      C i j k + C i k j + C j i k + C j k i + C k i j + C k j i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro k _
    dsimp only
    rw [show C i j k + C i k j + C j i k + C j k i + C k i j + C k j i = 0 from
      trilinear_six_term B hB (e i) (e j) (e k), smul_zero]
  have hcycle : cubicContraction T (fun i j k => C j k i) = cubicContraction T C := by
    calc
      _ = cubicContraction T (fun i j k => C i k j) := cubicContraction_swap12 T h12 _
      _ = _ := cubicContraction_swap23 T h23 C
  have hcycle' : cubicContraction T (fun i j k => C k i j) = cubicContraction T C := by
    calc
      _ = cubicContraction T (fun i j k => C j i k) := cubicContraction_swap23 T h23 _
      _ = _ := cubicContraction_swap12 T h12 C
  have hreverse : cubicContraction T (fun i j k => C k j i) = cubicContraction T C := by
    calc
      _ = cubicContraction T (fun i j k => C j k i) := cubicContraction_swap23 T h23 _
      _ = _ := hcycle
  simp only [cubicContraction, smul_add, Finset.sum_add_distrib] at hz
  change cubicContraction T C + cubicContraction T (fun i j k => C i k j) +
    cubicContraction T (fun i j k => C j i k) + cubicContraction T (fun i j k => C j k i) +
    cubicContraction T (fun i j k => C k i j) + cubicContraction T (fun i j k => C k j i) = 0 at hz
  rw [cubicContraction_swap23 T h23 C, cubicContraction_swap12 T h12 C,
    hcycle, hcycle', hreverse] at hz
  have h6 : (6 : ℝ) • cubicContraction T C = 0 := by
    calc
      _ = cubicContraction T C + cubicContraction T C + cubicContraction T C +
          cubicContraction T C + cubicContraction T C + cubicContraction T C := by module
      _ = 0 := hz
  exact (smul_eq_zero_iff_right (by norm_num : (6 : ℝ) ≠ 0)).mp h6

end Contraction
end
end OAI.Analysis.Calculus.Quaternion
