module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Dirichlet.Linearized
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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

open Filter Set
open scoped Topology

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

section Directional
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def directionalDerivative (f : E → F) (v : E) (x : E) : F := fderiv ℝ f x v

theorem contDiff_directionalDerivative {f : E → F} {m n : WithTop ENat}
    (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n) (v : E) :
    ContDiff ℝ m (directionalDerivative f v) :=
  (hf.fderiv_right hmn).clm_apply contDiff_const

theorem directionalDerivative_twice {f : E → F} (hf : ContDiff ℝ 2 f) (v w x : E) :
    directionalDerivative (directionalDerivative f w) v x =
      fderiv ℝ (fderiv ℝ f) x v w := by
  have hD := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  unfold directionalDerivative
  rw [fderiv_clm_apply (hD x) (differentiableAt_const w)]
  simp

theorem directionalDerivative_comm {f : E → F} (hf : ContDiff ℝ 2 f) (v w x : E) :
    directionalDerivative (directionalDerivative f w) v x =
      directionalDerivative (directionalDerivative f v) w x := by
  rw [directionalDerivative_twice hf, directionalDerivative_twice hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq v w

theorem directionalDerivative_triple_comm {f : E → F} (hf : ContDiff ℝ 3 f) (v i j x : E) :
    directionalDerivative (directionalDerivative (directionalDerivative f j) i) v x =
      directionalDerivative (directionalDerivative (directionalDerivative f v) j) i x := by
  have hj : ContDiff ℝ 2 (directionalDerivative f j) := contDiff_directionalDerivative hf (by norm_num) j
  rw [directionalDerivative_comm hj]
  have heq : directionalDerivative (directionalDerivative f j) v =
      directionalDerivative (directionalDerivative f v) j := by
    funext y
    exact directionalDerivative_comm (hf.of_le (by norm_num)) v j y
  rw [heq]

theorem hasDerivAt_directional_path {f : E → F} (hf : Differentiable ℝ f) (x v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ f (x + s • v)) (directionalDerivative f v (x + t • v)) t := by
  have hl : HasDerivAt (fun s : ℝ ↦ x + s • v) v t := by
    simpa using (((hasDerivAt_id t).smul_const v).const_add x)
  exact (hf (x + t • v)).hasFDerivAt.comp_hasDerivAt t hl

end Directional

theorem realHessian_eq_directional {n s : ℕ} {f : CoordinateSpace n s → ℝ}
    (hf : ContDiff ℝ 2 f) (x : CoordinateSpace n s) (i j : Fin n × Fin s) :
    realHessian f x i j = directionalDerivative
      (directionalDerivative f (coordinateVector j)) (coordinateVector i) x :=
  (directionalDerivative_twice hf _ _ _).symm

theorem hasDerivAt_realHessian_path {n s : ℕ} {f : CoordinateSpace n s → ℝ}
    (hf : ContDiff ℝ 3 f) (x v : CoordinateSpace n s) (t : ℝ) (i j : Fin n × Fin s) :
    HasDerivAt (fun a : ℝ ↦ realHessian f (x + a • v) i j)
      (realHessian (directionalDerivative f v) (x + t • v) i j) t := by
  have hj : ContDiff ℝ 2 (directionalDerivative f (coordinateVector j)) :=
    contDiff_directionalDerivative hf (by norm_num) _
  have hji : ContDiff ℝ 1 (directionalDerivative (directionalDerivative f (coordinateVector j)) (coordinateVector i)) :=
    contDiff_directionalDerivative hj (by norm_num) _
  have hpath := hasDerivAt_directional_path (hji.differentiable (by norm_num)) x v t
  rw [directionalDerivative_triple_comm hf] at hpath
  have hv : ContDiff ℝ 2 (directionalDerivative f v) := contDiff_directionalDerivative hf (by norm_num) v
  simpa only [realHessian_eq_directional (hf.of_le (by norm_num)), realHessian_eq_directional hv] using hpath

theorem hasDerivAt_quaternionHessian_path {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {f : CoordinateSpace n s → ℝ} (hf : ContDiff ℝ 3 f) (x v : CoordinateSpace n s)
    (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun a : ℝ ↦ quaternionHessian e f (x + a • v) i j)
      (quaternionHessian e (directionalDerivative f v) (x + t • v) i j) t := by
  unfold quaternionHessian OAI.Analysis.Calculus.Quaternion.hessianMap
  convert HasDerivAt.sum
    (u := Finset.univ) (fun α _ ↦ HasDerivAt.sum (u := Finset.univ)
      (fun β _ ↦ (hasDerivAt_realHessian_path hf x v t (i, α) (j, β)).smul_const (e α * star (e β)))) using 1
  funext a
  simp only [Finset.sum_apply]

theorem hasDerivAt_mooreHessian_path {n : ℕ} {f : CoordinateSpace n 4 → ℝ}
    (hf : ContDiff ℝ 3 f) (x v : CoordinateSpace n 4) (t : ℝ) :
    HasDerivAt (fun a : ℝ ↦ OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f (x + a • v)))
      (mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f) (directionalDerivative f v) (x + t • v)) t :=
  OAI.LinearAlgebra.Moore.hasDerivAt_mooreDet_path n _ _ t (hasDerivAt_quaternionHessian_path OAI.Analysis.Calculus.Quaternion.fourSlots hf x v t)

/-- Differentiating an actual local Monge–Ampère equation gives its actual
linearized equation, including commutation of the third derivatives. -/
theorem mooreLinearization_directional_eq {n : ℕ} {f F : CoordinateSpace n 4 → ℝ}
    (hf : ContDiff ℝ 3 f) {x : CoordinateSpace n 4} (v : CoordinateSpace n 4)
    (hF : DifferentiableAt ℝ F x)
    (heq : (fun y ↦ OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f y)) =ᶠ[𝓝 x] F) :
    mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f) (directionalDerivative f v) x =
      directionalDerivative F v x := by
  have hc : Continuous (fun a : ℝ ↦ x + a • v) := by fun_prop
  have ht : Tendsto (fun a : ℝ ↦ x + a • v) (𝓝 0) (𝓝 x) := by
    simpa using hc.tendsto 0
  have hD := (hasDerivAt_mooreHessian_path hf x v 0).congr_of_eventuallyEq (heq.comp_tendsto ht).symm
  have hFx : DifferentiableAt ℝ F (x + (0 : ℝ) • v) := by simpa using hF
  have hl : HasDerivAt (fun a : ℝ ↦ x + a • v) v 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x)
  have hFD := hFx.hasFDerivAt.comp_hasDerivAt 0 hl
  simpa only [zero_smul, add_zero, directionalDerivative] using hD.unique hFD

theorem mooreLinearization_directional_eq_on_open {n : ℕ} {f F : CoordinateSpace n 4 → ℝ}
    (hf : ContDiff ℝ 3 f) {Ω : Set (CoordinateSpace n 4)} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℝ F Ω)
    (heq : ∀ x ∈ Ω, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x) = F x)
    (v : CoordinateSpace n 4) {x : CoordinateSpace n 4} (hx : x ∈ Ω) :
    mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f) (directionalDerivative f v) x =
      directionalDerivative F v x := by
  apply mooreLinearization_directional_eq hf v ((hF x hx).differentiableAt (hΩ.mem_nhds hx))
  filter_upwards [hΩ.mem_nhds hx] with y hy
  exact heq y hy

end OAI.Analysis.PDE.Dirichlet
