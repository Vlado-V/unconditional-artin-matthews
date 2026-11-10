module

public import ArtinMatthews.SpectralFormMassGram
public import ArtinMatthews.SpectralCompactFormExceptional
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Meromorphic.Basic
public import ArtinMatthews.SpectralCompactPencilMeromorphic
public import ArtinMatthews.SpectralMeromorphicFormMaps
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! A genuine closed subspace of an ambient form has its own compact form
resolvent when the actual mass inclusion is compact on that subspace.
The weak equation retains the original ambient form pairing. -/
noncomputable section
open Set
open scoped InnerProductSpace
namespace ArtinMatthews

section
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace V] [CompleteSpace H] in
def spectralClosedFormInclusion (S : Submodule ℂ V) (J : V →L[ℂ] H) : S →L[ℂ] H :=
  J.comp S.subtypeL

def spectralClosedFormGram (S : Submodule ℂ V) (hS : IsClosed (S:Set V))
    (J : V →L[ℂ] H) : S →L[ℂ] S := by
  letI : CompleteSpace S := hS.isComplete.completeSpace_coe
  exact spectralFormMassGram (spectralClosedFormInclusion S J)

def spectralClosedFormExceptional (S : Submodule ℂ V) (hS : IsClosed (S:Set V))
    (J : V →L[ℂ] H) : Set ℂ :=
  spectralCompactFormExceptional (spectralClosedFormGram S hS J)

def spectralClosedFormWeakResolvent (S : Submodule ℂ V) (hS : IsClosed (S:Set V))
    (J : V →L[ℂ] H) (z : ℂ) : H →L[ℂ] S := by
  letI : CompleteSpace S := hS.isComplete.completeSpace_coe
  exact (Ring.inverse (spectralCompactFormPencil (spectralClosedFormGram S hS J) z)).comp
    (spectralClosedFormInclusion S J).adjoint

def spectralClosedFormResolvent (S : Submodule ℂ V) (hS : IsClosed (S:Set V))
    (J : V →L[ℂ] H) (z : ℂ) : H →L[ℂ] H :=
  (spectralClosedFormInclusion S J).comp (spectralClosedFormWeakResolvent S hS J z)

theorem spectralClosedFormGram_compact (S : Submodule ℂ V) (hS : IsClosed (S:Set V))
    (J : V →L[ℂ] H) (hJ : IsCompactOperator (spectralClosedFormInclusion S J)) :
    IsCompactOperator (spectralClosedFormGram S hS J) := by
  let _ : CompleteSpace S := hS.isComplete.completeSpace_coe
  exact spectralFormMassGram_compact (spectralClosedFormInclusion S J) hJ

theorem spectralClosedFormGram_symmetric (S : Submodule ℂ V) (hS : IsClosed (S:Set V))
    (J : V →L[ℂ] H) : (spectralClosedFormGram S hS J).toLinearMap.IsSymmetric := by
  let _ : CompleteSpace S := hS.isComplete.completeSpace_coe
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (spectralFormMassGram_selfAdjoint (spectralClosedFormInclusion S J))

theorem spectralClosedFormExceptional_finite_norm_le (S : Submodule ℂ V)
    (hS : IsClosed (S:Set V)) (J : V →L[ℂ] H)
    (hJ : IsCompactOperator (spectralClosedFormInclusion S J)) (R : ℝ) (hR : 0≤R) :
    {z : ℂ | z∈spectralClosedFormExceptional S hS J ∧ ‖z‖≤R}.Finite := by
  let _ : CompleteSpace S := hS.isComplete.completeSpace_coe
  exact spectralCompactFormExceptional_finite_norm_le (spectralClosedFormGram S hS J)
    (spectralClosedFormGram_compact S hS J hJ) (spectralClosedFormGram_symmetric S hS J) R hR

theorem spectralClosedFormExceptional_nonnegative (S : Submodule ℂ V)
    (hS : IsClosed (S:Set V)) (J : V →L[ℂ] H)
    (hJi : Function.Injective J) (hJb : ∀ u : S, ‖J u.val‖≤‖u‖)
    (z : ℂ) (hz : z ∈ spectralClosedFormExceptional S hS J) :
    ∃ r : ℝ, 0≤r ∧ z=(r:ℂ) := by
  let _ : CompleteSpace S := hS.isComplete.completeSpace_coe
  let K := spectralClosedFormInclusion S J
  have hKi : Function.Injective K := fun _ _ h => Subtype.ext (hJi h)
  have hKn : ‖K‖≤1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun u => by rw [one_mul];change ‖J u.val‖≤‖u‖;exact hJb u)
  obtain ⟨_,u,hu,he⟩ := spectralCompactFormExceptional_eigenvector (spectralClosedFormGram S hS J) z hz
  obtain ⟨t,ht,ht1,htz⟩ := spectralFormMassGram_eigenvalue_range K hKi hKn u hu ((z+1)⁻¹) he
  have he' : z+1=(t:ℂ)⁻¹ := by
    have h := congrArg (fun w : ℂ => w⁻¹) htz
    simpa only [inv_inv] using h
  have ht' : 1≤1/t := (le_div_iff₀ ht).mpr (by simpa only [one_mul] using ht1)
  refine ⟨1/t-1,by linarith,?_⟩
  rw [one_div,Complex.ofReal_sub,Complex.ofReal_inv,Complex.ofReal_one,← he',add_sub_cancel_right]

theorem spectralClosedFormResolvent_meromorphic (S : Submodule ℂ V) (hS : IsClosed (S:Set V))
    (J : V →L[ℂ] H) (hJ : IsCompactOperator (spectralClosedFormInclusion S J)) :
    Meromorphic (spectralClosedFormResolvent S hS J) := by
  let _ : CompleteSpace S := hS.isComplete.completeSpace_coe
  intro z
  have h := spectralCompactFormPencil_inverse_meromorphicAt (spectralClosedFormGram S hS J)
    (spectralClosedFormGram_compact S hS J hJ) (spectralClosedFormGram_symmetric S hS J) z
  exact spectralOperatorSandwich_meromorphicAt _ z h (spectralClosedFormInclusion S J)
    (spectralClosedFormInclusion S J).adjoint

theorem spectralClosedFormWeakResolvent_equation (S : Submodule ℂ V) (hS : IsClosed (S:Set V))
    (J : V →L[ℂ] H) (hJ : IsCompactOperator (spectralClosedFormInclusion S J))
    (z : ℂ) (hz : z∉spectralClosedFormExceptional S hS J) (F : H) (v : S) :
    let u := spectralClosedFormWeakResolvent S hS J z F
    inner ℂ v.val u.val-(z+1)*inner ℂ (J v.val) (J u.val)=inner ℂ (J v.val) F := by
  let _ : CompleteSpace S := hS.isComplete.completeSpace_coe
  let K := spectralClosedFormInclusion S J
  let P := spectralCompactFormPencil (spectralClosedFormGram S hS J) z
  let u := spectralClosedFormWeakResolvent S hS J z F
  have hP : IsUnit P := (spectralCompactFormPencil_isUnit_iff_notMem _
    (spectralClosedFormGram_compact S hS J hJ) z).mpr hz
  have he : P u=K.adjoint F := congrArg (fun A : S →L[ℂ] S => A (K.adjoint F))
    (Ring.mul_inverse_cancel P hP)
  have hi := congrArg (fun w : S => inner ℂ v w) he
  change inner ℂ v (u-(z+1) • spectralFormMassGram K u)=inner ℂ v (K.adjoint F) at hi
  rw [inner_sub_right,inner_smul_right,spectralFormMassGram_inner,K.adjoint_inner_right] at hi
  exact hi

end
end ArtinMatthews
