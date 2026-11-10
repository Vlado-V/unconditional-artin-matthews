module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Dirichlet.Quaternion
public import OAI.LinearAlgebra.Moore.Derivative
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
public import Mathlib.Topology.Sheaves.Init
public import OAI.LinearAlgebra.Moore.Elliptic
public import OAI.LinearAlgebra.Moore.Form
public import OAI.LinearAlgebra.Moore.Inverse


set_option backward.privateInPublic true
@[expose] public section

/-! Strict positivity of the real rank-one symbol of the quaternionic linearization. -/

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Matrix ComplexOrder

theorem quaternion_re_sum {ι : Type*} (s : Finset ι) (f : ι → Quaternion ℝ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

theorem quaternion_re_mul_comm (a b : Quaternion ℝ) : (a * b).re = (b * a).re := by
  simp only [Quaternion.re_mul]
  ring

theorem quaternionRealTrace_outer {n : ℕ}
    (C : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (g : Fin n → Quaternion ℝ) :
    (∑ i, ((C * OAI.Analysis.Calculus.Quaternion.outer g) i i).re) = (quaternionForm C g).re := by
  simp only [Matrix.mul_apply, OAI.Analysis.Calculus.Quaternion.outer, quaternionForm, quaternion_re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simpa only [mul_assoc] using quaternion_re_mul_comm (C i j * g j) (star (g i))

theorem mooreDifferential_outer_pos {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (g : Fin n → Quaternion ℝ)
    (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef) (hAC : A * C = 1) (hCA : C * A = 1)
    (hdet : 0 < OAI.LinearAlgebra.Moore.mooreDet n A) (hg : g ≠ 0) :
    0 < OAI.LinearAlgebra.Moore.mooreDifferential n A (OAI.Analysis.Calculus.Quaternion.outer g) := by
  have hC := OAI.LinearAlgebra.Moore.complexify_inverse_posDef n A C hA hAC
  have hq := (OAI.LinearAlgebra.Moore.complexify_posDef_iff (OAI.LinearAlgebra.Moore.isHermitian_of_complexify hC.isHermitian)).mp hC g hg
  rw [OAI.LinearAlgebra.Moore.mooreDifferential_inverse n A (OAI.Analysis.Calculus.Quaternion.outer g) C (OAI.LinearAlgebra.Moore.isHermitian_of_complexify hA.isHermitian)
    (OAI.Analysis.Calculus.Quaternion.outer_isHermitian g) hAC hCA, quaternionRealTrace_outer]
  exact mul_pos hdet hq

theorem moore_principalSymbol_pos {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (he : Function.Injective (OAI.Analysis.Calculus.Quaternion.gradientMap (m := Fin n) e))
    (A C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef) (hAC : A * C = 1) (hCA : C * A = 1)
    (hdet : 0 < OAI.LinearAlgebra.Moore.mooreDet n A) (ξ : Fin n × Fin s → ℝ) (hξ : ξ ≠ 0) :
    0 < OAI.LinearAlgebra.Moore.mooreDifferential n A (OAI.Analysis.Calculus.Quaternion.hessianMap e (fun i j ↦ ξ i * ξ j)) := by
  rw [OAI.Analysis.Calculus.Quaternion.hessianMap_rankOne]
  apply mooreDifferential_outer_pos A C _ hA hAC hCA hdet
  intro hg
  apply hξ
  apply he
  rw [hg]
  funext a
  simp [OAI.Analysis.Calculus.Quaternion.gradientMap]

/-- The real principal symbol is strictly positive in every nonzero four-slot direction. -/
theorem moore_fourSlot_principalSymbol_pos {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef) (hAC : A * C = 1) (hCA : C * A = 1)
    (hdet : 0 < OAI.LinearAlgebra.Moore.mooreDet n A) (ξ : Fin n × Fin 4 → ℝ) (hξ : ξ ≠ 0) :
    0 < OAI.LinearAlgebra.Moore.mooreDifferential n A (OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (fun i j ↦ ξ i * ξ j)) :=
  moore_principalSymbol_pos OAI.Analysis.Calculus.Quaternion.fourSlots OAI.Analysis.Calculus.Quaternion.gradientMap_fourSlots_injective A C hA hAC hCA hdet ξ hξ

/-- The same strict ellipticity holds for the original three-slot Hessian. -/
theorem moore_threeSlot_principalSymbol_pos {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef) (hAC : A * C = 1) (hCA : C * A = 1)
    (hdet : 0 < OAI.LinearAlgebra.Moore.mooreDet n A) (ξ : Fin n × Fin 3 → ℝ) (hξ : ξ ≠ 0) :
    0 < OAI.LinearAlgebra.Moore.mooreDifferential n A (OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.threeSlots (fun i j ↦ ξ i * ξ j)) :=
  moore_principalSymbol_pos OAI.Analysis.Calculus.Quaternion.threeSlots OAI.Analysis.Calculus.Quaternion.gradientMap_threeSlots_injective A C hA hAC hCA hdet ξ hξ

end OAI.Analysis.PDE.Dirichlet
