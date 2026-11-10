module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.AdelicSplitting.TestFamilyAction
public import OAI.RepresentationTheory.Weil.AdelicSplitting.GlobalKernel
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
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import OAI.RepresentationTheory.Weil.AdelicSplitting.PositiveTestFamily


set_option backward.privateInPublic true
@[expose] public section

/-! # Theta Scalar Kernel -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting

noncomputable section

/-! The actual theta functional respects the scalar relations defining
the adelic cover. This also proves faithfulness of its global circle. -/

open scoped Classical

variable (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.theta_place_scalar (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N)
    (v : ArchimedeanAdeles.Construction.Places F) (z : Circle) :
    (f.act F N ψ (RestrictedLimits.Construction.includePlace (Vacuum.Construction.coverIntegral F N ψ) v (Vacuum.Construction.scalarAt F N ψ v z))).theta F N =
      (z : ℂ) * f.theta F N := by
  apply f.theta_scalar F N ψ _ (fun w => if w = v then z else 1)
  · intro w
    by_cases hw : w = v
    · subst w
      simp
    · simp [hw]
  · convert! (hasProd_ite_eq v (z : ℂ)) using 1
    funext w
    split_ifs <;> rfl

theorem ThetaScalarKernel.Construction.restricted_place_scalar_central (v : ArchimedeanAdeles.Construction.Places F) (z : Circle)
    (a : Rational.Construction.RestrictedCover F N ψ) :
    Commute (RestrictedLimits.Construction.includePlace (Vacuum.Construction.coverIntegral F N ψ) v (Vacuum.Construction.scalarAt F N ψ v z)) a := by
  apply RestrictedProduct.ext
  intro w
  change RestrictedLimits.Construction.includePlace (Vacuum.Construction.coverIntegral F N ψ) v (Vacuum.Construction.scalarAt F N ψ v z) w * a w =
    a w * RestrictedLimits.Construction.includePlace (Vacuum.Construction.coverIntegral F N ψ) v (Vacuum.Construction.scalarAt F N ψ v z) w
  by_cases hw : w = v
  · subst w
    simp only [RestrictedLimits.Construction.includePlace_same]
    exact Oscillator.Construction.localScalar_central _ _ _ z (a v)
  · simp [hw]

theorem ThetaScalarKernel.Construction.scalarRelations_theta_fixed {a : Rational.Construction.RestrictedCover F N ψ}
    (ha : a ∈ CentralProduct.Construction.scalarRelations (Vacuum.Construction.coverIntegral F N ψ) (Vacuum.Construction.scalarAt F N ψ)) :
    a ∈ TestFamilyAction.Construction.thetaStabilizer F N ψ := by
  obtain ⟨v, w, z, rfl⟩ := ha
  intro f
  rw [f.act_mul F N ψ, RestrictedTestFamilies.Construction.RestrictedTestFamily.theta_place_scalar]
  have hinv : (RestrictedLimits.Construction.includePlace (Vacuum.Construction.coverIntegral F N ψ) w (Vacuum.Construction.scalarAt F N ψ w z))⁻¹ =
      RestrictedLimits.Construction.includePlace (Vacuum.Construction.coverIntegral F N ψ) w (Vacuum.Construction.scalarAt F N ψ w z⁻¹) := by simp
  rw [hinv, f.theta_place_scalar F N ψ]
  simp

theorem ThetaScalarKernel.Construction.scalarKernel_le_thetaStabilizer :
    CentralProduct.Construction.scalarKernel (Vacuum.Construction.coverIntegral F N ψ) (Vacuum.Construction.scalarAt F N ψ) ≤ TestFamilyAction.Construction.thetaStabilizer F N ψ := by
  let H : Subgroup (Rational.Construction.RestrictedCover F N ψ) :=
    Subgroup.center (Rational.Construction.RestrictedCover F N ψ) ⊓ TestFamilyAction.Construction.thetaStabilizer F N ψ
  let : H.Normal := ⟨fun a ha b => by
    have hc : b * a = a * b := (Subgroup.mem_center_iff.mp ha.1) b
    have he : b * a * b⁻¹ = a := by rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    simpa only [he] using ha⟩
  apply le_trans (Subgroup.normalClosure_le_normal (N := H) ?_) inf_le_right
  rintro a ha
  refine ⟨?_, ThetaScalarKernel.Construction.scalarRelations_theta_fixed F N ψ ha⟩
  obtain ⟨v, w, z, rfl⟩ := ha
  apply Subgroup.mem_center_iff.mpr
  intro b
  exact ((ThetaScalarKernel.Construction.restricted_place_scalar_central F N ψ v z b).mul_left
    (ThetaScalarKernel.Construction.restricted_place_scalar_central F N ψ w z b).inv_left).eq.symm

theorem ThetaScalarKernel.Construction.theta_eq_of_assemble_eq (a b : Rational.Construction.RestrictedCover F N ψ)
    (hab : Rational.Construction.assembleGlobalCover F N ψ a = Rational.Construction.assembleGlobalCover F N ψ b)
    (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    (f.act F N ψ a).theta F N = (f.act F N ψ b).theta F N := by
  have hk : a * b⁻¹ ∈ CentralProduct.Construction.scalarKernel (Vacuum.Construction.coverIntegral F N ψ) (Vacuum.Construction.scalarAt F N ψ) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change Rational.Construction.assembleGlobalCover F N ψ (a * b⁻¹) = 1
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have h := ThetaScalarKernel.Construction.scalarKernel_le_thetaStabilizer F N ψ hk (f.act F N ψ b)
  rw [← f.act_mul F N ψ, inv_mul_cancel_right] at h
  exact h

def ThetaScalarKernel.Construction.globalTheta (a : Vacuum.Construction.GlobalCover F N ψ) (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) : ℂ :=
  Quotient.liftOn a (fun b => (f.act F N ψ b).theta F N)
    (fun a b h => ThetaScalarKernel.Construction.theta_eq_of_assemble_eq F N ψ a b (Quotient.sound h) f)

theorem ThetaScalarKernel.Construction.globalTheta_assemble (a : Rational.Construction.RestrictedCover F N ψ) (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    ThetaScalarKernel.Construction.globalTheta F N ψ (Rational.Construction.assembleGlobalCover F N ψ a) f = (f.act F N ψ a).theta F N := rfl

theorem ThetaScalarKernel.Construction.globalTheta_one (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) : ThetaScalarKernel.Construction.globalTheta F N ψ 1 f = f.theta F N := by
  change (f.act F N ψ 1).theta F N = _
  rw [f.act_one F N ψ]

theorem ThetaScalarKernel.Construction.globalTheta_scalar (v : ArchimedeanAdeles.Construction.Places F) (z : Circle) (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    ThetaScalarKernel.Construction.globalTheta F N ψ (GlobalKernel.Construction.globalScalar F N ψ v z) f = (z : ℂ) * f.theta F N :=
  f.theta_place_scalar F N ψ v z

theorem ThetaScalarKernel.Construction.globalScalar_injective (v : ArchimedeanAdeles.Construction.Places F) : Function.Injective (GlobalKernel.Construction.globalScalar F N ψ v) := by
  apply (injective_iff_map_eq_one _).mpr
  intro z hz
  obtain ⟨f, hf⟩ := PositiveTestFamily.Construction.exists_theta_nonzero F N
  have h := congrArg (fun a => ThetaScalarKernel.Construction.globalTheta F N ψ a f) hz
  rw [ThetaScalarKernel.Construction.globalTheta_scalar, ThetaScalarKernel.Construction.globalTheta_one] at h
  have hzC : (z : ℂ) = 1 := mul_right_cancel₀ hf (h.trans (one_mul _).symm)
  exact Subtype.ext hzC

end

end OAI.RepresentationTheory.Weil.AdelicSplitting
