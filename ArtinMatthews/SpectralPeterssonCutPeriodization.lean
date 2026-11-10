module

public import ArtinMatthews.SpectralPeterssonCutRows
public import ArtinMatthews.SpectralPeterssonParabolicUnfold
public import ArtinMatthews.SpectralFourierBruhatKernel
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

/-! The sharp cut is the actual parabolic Poincare periodization. The
unit strip selects one translation of every signed source row. -/
noncomputable section
open Set Matrix UpperHalfPlane
open scoped MatrixGroups

namespace ArtinMatthews

def spectralPeterssonHeightCutSeed (n : ℕ+) (A : ℝ) (z : UpperHalfPlane) : ℂ :=
  if A < 4*Real.pi*(n : ℝ)*z.im then spectralHolomorphicCuspSeed (n : ℕ) z else 0

def spectralPeterssonStripCutSeed (n : ℕ+) (A : ℝ) : UpperHalfPlane → ℂ :=
  (hyperbolicCuspStrip 1 0).indicator (spectralPeterssonHeightCutSeed n A)

theorem spectralPeterssonHeightCutSeed_slash (k : ℕ) (n : ℕ+) (A : ℝ)
    (G : SL(2, ℝ)) (z : UpperHalfPlane) :
    spectralHolomorphicSlash k G (spectralPeterssonHeightCutSeed n A) z =
      if A < 4*Real.pi*(n : ℝ)*(G • z).im then
        spectralHolomorphicSlash k G (spectralHolomorphicCuspSeed (n : ℕ)) z else 0 := by
  rw [spectralHolomorphicSlash_apply]
  unfold spectralPeterssonHeightCutSeed
  split_ifs <;> simp only [spectralHolomorphicSlash_apply,zero_div]

theorem gamma0PeterssonCutRow_eq_slash (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (n : ℕ+) (A : ℝ) (p : Gamma0PeterssonSignedRow N 1 a) (z : UpperHalfPlane) :
    gamma0PeterssonCutRow N a k n A p z =
      spectralHolomorphicSlash k (gamma0TrueWidthMatrix N 1 a (gamma0PeterssonRowMatrix N 1 a p).val)
        (spectralPeterssonHeightCutSeed n A) z := by
  rw [spectralPeterssonHeightCutSeed_slash]
  rfl

theorem spectralPeterssonHeightCutSeed_translate (n : ℕ+) (A : ℝ) (l : ℤ)
    (z : UpperHalfPlane) :
    spectralPeterssonHeightCutSeed n A (realTranslation (l : ℝ) • z) =
      spectralPeterssonHeightCutSeed n A z := by
  have hseed := congrFun (spectralHolomorphicCuspSeed_slash_translation 0 (n : ℕ) l) z
  rw [spectralHolomorphicSlash_apply,pow_zero,div_one] at hseed
  simp only [spectralPeterssonHeightCutSeed,realTranslation_im_smul,hseed]

theorem spectralPeterssonStripCutSeed_translate (k : ℕ) (n : ℕ+) (A : ℝ) (l : ℤ)
    (z : UpperHalfPlane) :
    spectralHolomorphicSlash k (realTranslation (l : ℝ)) (spectralPeterssonStripCutSeed n A) z =
      if l = spectralPeterssonStripLift z.re then spectralPeterssonHeightCutSeed n A z else 0 := by
  have hdenom : ((((realTranslation (l : ℝ)) 1 0 : ℝ) : ℂ)*(z : ℂ)+
      (((realTranslation (l : ℝ)) 1 1 : ℝ) : ℂ)) = 1 := by simp [realTranslation]
  rw [spectralHolomorphicSlash_apply,hdenom,one_pow,div_one]
  have hmem : realTranslation (l : ℝ) • z ∈ hyperbolicCuspStrip 1 0 ↔
      l = spectralPeterssonStripLift z.re := by
    change ((realTranslation (l : ℝ) • z).re ∈ Ioc (0 : ℝ) 1 ∧
      0 < (realTranslation (l : ℝ) • z).im) ↔ _
    rw [realTranslation_re_smul,realTranslation_im_smul]
    constructor
    · intro h
      exact spectralPeterssonStripLift_unique z.re l h.1
    · intro h
      rw [h]
      exact ⟨spectralPeterssonStripLift_mem z.re,z.im_pos⟩
  unfold spectralPeterssonStripCutSeed
  by_cases hl : l = spectralPeterssonStripLift z.re
  · rw [indicator_of_mem (hmem.mpr hl),if_pos hl,spectralPeterssonHeightCutSeed_translate]
  · rw [indicator_of_notMem (fun h => hl (hmem.mp h)),if_neg hl]

theorem gamma0PeterssonCutParabolic_value (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (n : ℕ+) (A : ℝ) (p : Gamma0PeterssonSignedRow N 1 a) (l : ℤ)
    (z : UpperHalfPlane) :
    spectralHolomorphicSlash k ((gamma0TrueCuspScaling N a)⁻¹*
      atkinRealMap (gamma0PeterssonParabolicExpand N a (p,l)).val)
      (spectralPeterssonStripCutSeed n A) z =
      if l = spectralPeterssonStripLift
          ((gamma0TrueWidthMatrix N 1 a (gamma0PeterssonRowMatrix N 1 a p).val) • z).re
      then gamma0PeterssonCutRow N a k n A p z else 0 := by
  rw [gamma0PeterssonParabolicExpand_normalized,spectralHolomorphicSlash_mul,
    spectralHolomorphicSlash_apply,spectralPeterssonStripCutSeed_translate]
  split_ifs with h
  · rw [gamma0PeterssonCutRow_eq_slash,spectralHolomorphicSlash_apply]
  · exact zero_div _

theorem gamma0PeterssonTruncatedPoincare_periodization (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (n : ℕ+) (A : ℝ) (z : UpperHalfPlane) :
    gamma0PeterssonTruncatedPoincare N a k n A z =
      (1/2 : ℂ)*∑' γ : CongruenceSubgroup.Gamma0 N,
        spectralHolomorphicSlash k ((gamma0TrueCuspScaling N a)⁻¹*atkinRealMap γ.val)
          (spectralPeterssonStripCutSeed n A) z := by
  let e := gamma0PeterssonParabolicEquiv N a
  let L (p : Gamma0PeterssonSignedRow N 1 a) := spectralPeterssonStripLift
    ((gamma0TrueWidthMatrix N 1 a (gamma0PeterssonRowMatrix N 1 a p).val) • z).re
  let E (p : Gamma0PeterssonSignedRow N 1 a) := e (p,L p)
  let f (γ : CongruenceSubgroup.Gamma0 N) :=
    spectralHolomorphicSlash k ((gamma0TrueCuspScaling N a)⁻¹*atkinRealMap γ.val)
      (spectralPeterssonStripCutSeed n A) z
  have hE : Function.Injective E := fun p q h => congrArg Prod.fst (e.injective h)
  have hvalue (p : Gamma0PeterssonSignedRow N 1 a) (l : ℤ) :
      f (e (p,l)) = if l = L p then gamma0PeterssonCutRow N a k n A p z else 0 :=
    gamma0PeterssonCutParabolic_value N a k n A p l z
  have hsupport : Function.support f ⊆ range E := by
    intro γ hγ
    let p := e.symm γ
    have hp : e (p.1,p.2) = γ := by simpa only [Prod.eta] using e.apply_symm_apply γ
    have hl : p.2 = L p.1 := by
      by_contra h
      apply hγ
      rw [← hp,hvalue,if_neg h]
    exact ⟨p.1,by change e (p.1,L p.1) = γ; rw [← hl,hp]⟩
  unfold gamma0PeterssonTruncatedPoincare
  congr 1
  calc
    _ = ∑' p, f (E p) := by
      apply tsum_congr
      intro p
      have h := hvalue p (L p)
      rw [if_pos rfl] at h
      exact h.symm
    _ = _ := hE.tsum_eq hsupport

end ArtinMatthews
