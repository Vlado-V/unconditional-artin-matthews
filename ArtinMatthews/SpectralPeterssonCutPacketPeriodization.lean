module

public import ArtinMatthews.SpectralPeterssonCutPacket
public import ArtinMatthews.SpectralFourierBruhatKernel
public import ArtinMatthews.SpectralPeterssonWeightedNorm
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The full congruence-group periodization of a cut packet records
exactly one translate of each original signed parabolic row. -/
noncomputable section
open Set Matrix UpperHalfPlane
open scoped MatrixGroups BigOperators

namespace ArtinMatthews

variable {ι : Type*}

def spectralPeterssonStripCutPacket (k : ℕ) (t : Finset ι) (α : ι → ℂ)
    (n : ι → ℕ+) (A : ℝ) : UpperHalfPlane → ℂ :=
  (hyperbolicCuspStrip 1 0).indicator (spectralPeterssonCutPacketSeed k t α n A)

theorem spectralPeterssonStripCutPacket_eq_sum (k : ℕ) (t : Finset ι) (α : ι → ℂ)
    (n : ι → ℕ+) (A : ℝ) (z : UpperHalfPlane) :
    spectralPeterssonStripCutPacket k t α n A z =
      ∑ j ∈ t, α j*(spectralPeterssonNormalization k (n j) : ℂ)*spectralPeterssonStripCutSeed (n j) A z := by
  classical
  by_cases hz : z ∈ hyperbolicCuspStrip 1 0
  · simp only [spectralPeterssonStripCutPacket,spectralPeterssonStripCutSeed,
      indicator_of_mem hz,spectralPeterssonCutPacketSeed]
  · simp only [spectralPeterssonStripCutPacket,spectralPeterssonStripCutSeed,
      indicator_of_notMem hz,mul_zero,Finset.sum_const_zero]

theorem spectralPeterssonStripCutPacket_translate (k : ℕ) (t : Finset ι) (α : ι → ℂ)
    (n : ι → ℕ+) (A : ℝ) (l : ℤ) (z : UpperHalfPlane) :
    spectralHolomorphicSlash k (realTranslation (l : ℝ))
      (spectralPeterssonStripCutPacket k t α n A) z =
      if l = spectralPeterssonStripLift z.re then spectralPeterssonCutPacketSeed k t α n A z else 0 := by
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
  unfold spectralPeterssonStripCutPacket
  by_cases hl : l = spectralPeterssonStripLift z.re
  · rw [indicator_of_mem (hmem.mpr hl),if_pos hl,spectralPeterssonCutPacketSeed_translate]
  · rw [indicator_of_notMem (fun h => hl (hmem.mp h)),if_neg hl]

theorem gamma0PeterssonCutPacketParabolic_value (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+) (A : ℝ)
    (p : Gamma0PeterssonSignedRow N 1 a) (l : ℤ) (z : UpperHalfPlane) :
    spectralHolomorphicSlash k ((gamma0TrueCuspScaling N a)⁻¹*
      atkinRealMap (gamma0PeterssonParabolicExpand N a (p,l)).val)
      (spectralPeterssonStripCutPacket k t α n A) z =
      if l = spectralPeterssonStripLift
          ((gamma0TrueWidthMatrix N 1 a (gamma0PeterssonRowMatrix N 1 a p).val) • z).re
      then gamma0PeterssonCutPacketRow N a k t α n A p z else 0 := by
  rw [gamma0PeterssonParabolicExpand_normalized,spectralHolomorphicSlash_mul,
    spectralHolomorphicSlash_apply,spectralPeterssonStripCutPacket_translate]
  split_ifs with h
  · rw [gamma0PeterssonCutPacketRow_eq_slash,spectralHolomorphicSlash_apply]
  · exact zero_div _

theorem gamma0PeterssonCutPacket_square_periodization (N : ℕ) [NeZero N]
    (a : SL(2, ℤ)) (k : ℕ) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+) (A : ℝ)
    (z : UpperHalfPlane) :
    (∑' p : Gamma0PeterssonSignedRow N 1 a,
      ‖gamma0PeterssonCutPacketRow N a k t α n A p z‖^2*z.im^k) =
    ∑' γ : CongruenceSubgroup.Gamma0 N,
      ‖spectralPeterssonStripCutPacket k t α n A
          (((gamma0TrueCuspScaling N a)⁻¹*atkinRealMap γ.val) • z)‖^2*
        (((gamma0TrueCuspScaling N a)⁻¹*atkinRealMap γ.val) • z).im^k := by
  let e := gamma0PeterssonParabolicEquiv N a
  let L (p : Gamma0PeterssonSignedRow N 1 a) := spectralPeterssonStripLift
    ((gamma0TrueWidthMatrix N 1 a (gamma0PeterssonRowMatrix N 1 a p).val) • z).re
  let E (p : Gamma0PeterssonSignedRow N 1 a) := e (p,L p)
  let F (γ : CongruenceSubgroup.Gamma0 N) :=
    ‖spectralHolomorphicSlash k ((gamma0TrueCuspScaling N a)⁻¹*atkinRealMap γ.val)
      (spectralPeterssonStripCutPacket k t α n A) z‖^2*z.im^k
  have hE : Function.Injective E := fun p q h => congrArg Prod.fst (e.injective h)
  have hvalue (p : Gamma0PeterssonSignedRow N 1 a) (l : ℤ) :
      F (e (p,l)) = if l = L p then
        ‖gamma0PeterssonCutPacketRow N a k t α n A p z‖^2*z.im^k else 0 := by
    change ‖spectralHolomorphicSlash k ((gamma0TrueCuspScaling N a)⁻¹*
      atkinRealMap (gamma0PeterssonParabolicExpand N a (p,l)).val)
      (spectralPeterssonStripCutPacket k t α n A) z‖^2*z.im^k = _
    rw [gamma0PeterssonCutPacketParabolic_value]
    split_ifs <;> simp only [norm_zero,zero_pow (by omega : 2 ≠ 0),zero_mul]
  have hsupport : Function.support F ⊆ range E := by
    intro γ hγ
    let p := e.symm γ
    have hp : e (p.1,p.2) = γ := by simpa only [Prod.eta] using e.apply_symm_apply γ
    have hl : p.2 = L p.1 := by
      by_contra h
      apply hγ
      rw [← hp,hvalue,if_neg h]
    exact ⟨p.1,by change e (p.1,L p.1) = γ; rw [← hl,hp]⟩
  calc
    _ = ∑' p, F (E p) := by
      apply tsum_congr
      intro p
      have h := hvalue p (L p)
      rw [if_pos rfl] at h
      exact h.symm
    _ = ∑' γ, F γ := hE.tsum_eq hsupport
    _ = _ := by
      apply tsum_congr
      intro γ
      exact spectralHolomorphicSlash_norm_sq_weight k _ _ z

end ArtinMatthews
