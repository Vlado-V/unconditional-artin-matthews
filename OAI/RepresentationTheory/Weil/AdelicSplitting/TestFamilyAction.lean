module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaTest
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


set_option backward.privateInPublic true
@[expose] public section

/-! # Test Family Action -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting

noncomputable section

section

/-! Action laws and exact scalar-product behavior for restricted test
families and their convergent theta sums. -/

open scoped Classical _root_.NumberField

variable (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)

@[ext] theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.ext {f g : RestrictedTestFamilies.Construction.RestrictedTestFamily F N}
    (h : ∀ v, f v = g v) : f = g := by
  cases f
  cases g
  congr 1
  exact funext h

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.act_one (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) : f.act F N ψ 1 = f := by
  apply RestrictedTestFamilies.Construction.RestrictedTestFamily.ext
  intro v
  change Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v) 1 (f v) = f v
  rw [map_one]
  rfl

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.act_mul (a b : Rational.Construction.RestrictedCover F N ψ) (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    f.act F N ψ (a * b) = (f.act F N ψ b).act F N ψ a := by
  apply RestrictedTestFamilies.Construction.RestrictedTestFamily.ext
  intro v
  change Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v) (a v * b v) (f v) = _
  rw [map_mul]
  rfl

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.scalar_value (a : Rational.Construction.RestrictedCover F N ψ) (z : ArchimedeanAdeles.Construction.Places F → Circle)
    (ha : ∀ v, a v = Vacuum.Construction.scalarAt F N ψ v (z v)) (c : ℂ)
    (hc : HasProd (fun v => (z v : ℂ)) c) (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (x : Fin N → ArchimedeanAdeles.Construction.Adeles F) :
    (f.act F N ψ a).value F N x = c * f.value F N x := by
  apply ((f.act F N ψ a).localValue_hasProd F N x).unique
  apply (hc.mul (f.localValue_hasProd F N x)).congr_fun
  intro v
  change (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v) (a v) (f v)).val _ = _
  rw [ha v]
  rfl

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.theta_scalar (a : Rational.Construction.RestrictedCover F N ψ) (z : ArchimedeanAdeles.Construction.Places F → Circle)
    (ha : ∀ v, a v = Vacuum.Construction.scalarAt F N ψ v (z v)) (c : ℂ)
    (hc : HasProd (fun v => (z v : ℂ)) c) (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    (f.act F N ψ a).theta F N = c * f.theta F N := by
  change (∑' q : Fin N → F, (f.act F N ψ a).value F N
      (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i))) = _
  simp_rw [f.scalar_value F N ψ a z ha c hc]
  exact tsum_mul_left

def TestFamilyAction.Construction.thetaStabilizer : Subgroup (Rational.Construction.RestrictedCover F N ψ) where
  carrier := {a | ∀ f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N, (f.act F N ψ a).theta F N = f.theta F N}
  one_mem' f := by rw [f.act_one F N ψ]
  mul_mem' ha hb f := by rw [f.act_mul F N ψ, ha, hb]
  inv_mem' {a} ha f := by
    have h := ha (f.act F N ψ a⁻¹)
    rw [← f.act_mul F N ψ, mul_inv_cancel, f.act_one F N ψ] at h
    exact h.symm

def TestFamilyAction.Construction.positiveThetaSubgroup : Subgroup (Rational.Construction.RestrictedCover F N ψ) where
  carrier := {a | ∀ f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N,
    ∃ c : ℝ, 0 < c ∧ (f.act F N ψ a).theta F N = (c : ℂ) * f.theta F N}
  one_mem' f := ⟨1, by norm_num, by rw [f.act_one F N ψ, Complex.ofReal_one, one_mul]⟩
  mul_mem' ha hb f := by
    obtain ⟨d, hd, hdb⟩ := hb f
    obtain ⟨c, hc, hca⟩ := ha (f.act F N ψ _)
    exact ⟨c * d, mul_pos hc hd, by rw [f.act_mul F N ψ, hca, hdb, Complex.ofReal_mul, mul_assoc]⟩
  inv_mem' {a} ha f := by
    obtain ⟨c, hc, h⟩ := ha (f.act F N ψ a⁻¹)
    rw [← f.act_mul F N ψ, mul_inv_cancel, f.act_one F N ψ] at h
    refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
    rw [Complex.ofReal_inv, h, ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne'), one_mul]

theorem TestFamilyAction.Construction.thetaStabilizer_le_positiveThetaSubgroup :
    TestFamilyAction.Construction.thetaStabilizer F N ψ ≤ TestFamilyAction.Construction.positiveThetaSubgroup F N ψ := by
  intro a ha f
  exact ⟨1, by norm_num, by simpa only [Complex.ofReal_one, one_mul] using ha f⟩

end

/-! Products of local scalar relations for actual restricted test families. -/

open scoped Classical _root_.NumberField

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.value_of_local_scalars (f g : RestrictedTestFamilies.Construction.RestrictedTestFamily F N)
    (z : ArchimedeanAdeles.Construction.Places F → ℂ) (c : ℂ) (hz : HasProd z c)
    (hfg : ∀ v x, (f v).val x = z v * (g v).val x) (x : Fin N → ArchimedeanAdeles.Construction.Adeles F) :
    f.value F N x = c * g.value F N x := by
  apply (f.localValue_hasProd F N x).unique
  exact (hz.mul (g.localValue_hasProd F N x)).congr_fun (fun v => hfg v _)

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.theta_of_local_scalars (f g : RestrictedTestFamilies.Construction.RestrictedTestFamily F N)
    (z : ArchimedeanAdeles.Construction.Places F → ℂ) (c : ℂ) (hz : HasProd z c)
    (hfg : ∀ v x, (f v).val x = z v * (g v).val x) :
    f.theta F N = c * g.theta F N := by
  change (∑' q : Fin N → F, f.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i))) = _
  simp_rw [f.value_of_local_scalars F N g z c hz hfg]
  exact tsum_mul_left

end

end OAI.RepresentationTheory.Weil.AdelicSplitting
