module

public import ArtinMatthews.SpectralPeterssonParabolicUnfold
public import ArtinMatthews.SpectralModularPartitionGamma0
public import ArtinMatthews.SpectralPeterssonPoincare
public import ArtinMatthews.SpectralFourierBruhatKernel
public import ArtinMatthews.SpectralPeterssonPoincareAction
public import ArtinMatthews.SpectralPeterssonRegionUnfolding
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
public import Mathlib.RingTheory.SimpleRing.Principal
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

/-! The actual Petersson pairing unfolds over the literal normalized
cusp strip. The two central representatives cancel exactly. -/

noncomputable section
open Set MeasureTheory Matrix UpperHalfPlane
open scoped MatrixGroups ComplexConjugate

namespace ArtinMatthews

def gamma0PeterssonInner (N k : ℕ) (F G : UpperHalfPlane → ℂ) : ℂ :=
  ∫ z in gamma0InteriorRegion N, UpperHalfPlane.petersson (k : ℤ) F G z

def spectralPeterssonStripIntegrand (k : ℕ) (n : ℕ+) (F : UpperHalfPlane → ℂ) :
    UpperHalfPlane → ℂ :=
  (hyperbolicCuspStrip 1 0).indicator
    (UpperHalfPlane.petersson (k : ℤ) (spectralHolomorphicCuspSeed (n : ℕ)) F)

def gamma0PeterssonUnfoldedIntegrand (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (n : ℕ+) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  spectralPeterssonStripIntegrand k n (spectralHolomorphicSlash k (gamma0TrueCuspScaling N a) F)
    ((gamma0TrueCuspScaling N a)⁻¹ • z)

theorem gamma0PeterssonUnfoldedIntegrand_translate (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (n : ℕ+) (F : UpperHalfPlane → ℂ)
    (hF : ∀ γ : CongruenceSubgroup.Gamma0 N, spectralHolomorphicSlash k (atkinRealMap γ.val) F = F)
    (p : Gamma0PeterssonSignedRow N 1 a) (l : ℤ) (z : UpperHalfPlane) :
    let G := gamma0TrueWidthMatrix N 1 a (gamma0PeterssonRowMatrix N 1 a p).val
    gamma0PeterssonUnfoldedIntegrand N a k n F ((gamma0PeterssonParabolicExpand N a (p,l)).val • z) =
      if l = spectralPeterssonStripLift (G • z).re then
        UpperHalfPlane.petersson (k : ℤ) (gamma0PeterssonSignedSummand N 1 a k (n : ℕ) p) F z
      else 0 := by
  dsimp only
  let G := gamma0TrueWidthMatrix N 1 a (gamma0PeterssonRowMatrix N 1 a p).val
  let γ := gamma0PeterssonParabolicExpand N a (p,l)
  let σ := gamma0TrueCuspScaling N a
  let H := σ⁻¹*atkinRealMap γ.val
  have hH : H = realTranslation (l : ℝ)*G := gamma0PeterssonParabolicExpand_normalized N a p l
  have hσ : σ⁻¹ • (γ.val • z) = H • z := by
    change _ = (σ⁻¹*atkinRealMap γ.val) • z
    rw [mul_smul,atkinRealMap_smul]
  have ha : spectralHolomorphicSlash k H (spectralHolomorphicCuspSeed (n : ℕ)) =
      gamma0PeterssonSignedSummand N 1 a k (n : ℕ) p := by
    rw [hH,spectralHolomorphicSlash_mul,spectralHolomorphicCuspSeed_slash_translation]
    rfl
  have hb : spectralHolomorphicSlash k H (spectralHolomorphicSlash k σ F) = F := by
    rw [← spectralHolomorphicSlash_mul,show σ*H = atkinRealMap γ.val by dsimp only [H]; group]
    exact hF γ
  have hp := spectralHolomorphicPetersson_slash k H (spectralHolomorphicCuspSeed (n : ℕ))
    (spectralHolomorphicSlash k σ F) z
  rw [ha,hb] at hp
  have hmem : H • z ∈ hyperbolicCuspStrip 1 0 ↔ l = spectralPeterssonStripLift (G • z).re := by
    rw [hH,mul_smul]
    change ((realTranslation (l : ℝ) • (G • z)).re ∈ Ioc (0 : ℝ) 1 ∧
      0 < (realTranslation (l : ℝ) • (G • z)).im) ↔ _
    rw [realTranslation_re_smul]
    constructor
    · intro h
      exact spectralPeterssonStripLift_unique _ l h.1
    · intro h
      rw [h]
      exact ⟨spectralPeterssonStripLift_mem _,(realTranslation _ • (G • z)).im_pos⟩
  unfold gamma0PeterssonUnfoldedIntegrand spectralPeterssonStripIntegrand
  rw [hσ]
  classical
  by_cases hl : l = spectralPeterssonStripLift (G • z).re
  · rw [indicator_of_mem (hmem.mpr hl),if_pos hl,← hp]
  · rw [indicator_of_notMem (fun hm => hl (hmem.mp hm)),if_neg hl]

theorem gamma0PeterssonUnfoldedIntegrand_periodize (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (hk : 3 ≤ k) (hEven : Even k) (n : ℕ+) (F : UpperHalfPlane → ℂ)
    (hF : ∀ γ : CongruenceSubgroup.Gamma0 N, spectralHolomorphicSlash k (atkinRealMap γ.val) F = F)
    (z : UpperHalfPlane) :
    (∑' γ : CongruenceSubgroup.Gamma0 N, gamma0PeterssonUnfoldedIntegrand N a k n F (γ.val⁻¹ • z)) =
      (2 : ℂ)*UpperHalfPlane.petersson (k : ℤ) (gamma0PeterssonPoincare N a k (n : ℕ)) F z := by
  let e := gamma0PeterssonParabolicEquiv N a
  let L (p : Gamma0PeterssonSignedRow N 1 a) := spectralPeterssonStripLift
    ((gamma0TrueWidthMatrix N 1 a (gamma0PeterssonRowMatrix N 1 a p).val) • z).re
  let E (p : Gamma0PeterssonSignedRow N 1 a) := e (p,L p)
  let f (γ : CongruenceSubgroup.Gamma0 N) := gamma0PeterssonUnfoldedIntegrand N a k n F (γ.val • z)
  let A (p : Gamma0PeterssonSignedRow N 1 a) := gamma0PeterssonSignedSummand N 1 a k (n : ℕ) p z
  have hE : Function.Injective E := fun p q h => congrArg Prod.fst (e.injective h)
  have hvalue (p : Gamma0PeterssonSignedRow N 1 a) (l : ℤ) :
      f (e (p,l)) = if l = L p then
        UpperHalfPlane.petersson (k : ℤ) (gamma0PeterssonSignedSummand N 1 a k (n : ℕ) p) F z
      else 0 :=
    gamma0PeterssonUnfoldedIntegrand_translate N a k n F hF p l z
  have hsup : Function.support f ⊆ range E := by
    intro γ hγ
    let p := e.symm γ
    have hp : e (p.1,p.2) = γ := by simpa only [Prod.eta] using e.apply_symm_apply γ
    have hl : p.2 = L p.1 := by
      by_contra hh
      apply hγ
      rw [← hp,hvalue,if_neg hh]
    exact ⟨p.1, by change e (p.1,L p.1) = γ; rw [← hl,hp]⟩
  have hsum : (∑' p, A p) = (2 : ℂ)*gamma0PeterssonPoincare N a k (n : ℕ) z := by
    unfold gamma0PeterssonPoincare
    rw [gamma0PeterssonPoincareChart_signed_sum N 1 a k (n : ℕ) hk hEven]
    change (∑' p, A p) = (2 : ℂ)*((1/2 : ℂ)*(∑' p, A p))
    ring
  calc
    _ = ∑' γ, f γ := by
      simpa only [f,Equiv.inv_apply,Subgroup.coe_inv] using
        (Equiv.inv (CongruenceSubgroup.Gamma0 N)).tsum_eq f
    _ = ∑' p, f (E p) := (hE.tsum_eq hsup).symm
    _ = ∑' p, UpperHalfPlane.petersson (k : ℤ) (gamma0PeterssonSignedSummand N 1 a k (n : ℕ) p) F z := by
      apply tsum_congr
      intro p
      exact (hvalue p (L p)).trans (if_pos rfl)
    _ = _ := by
      unfold UpperHalfPlane.petersson
      change (∑' p, conj (A p)*F z*(z.im : ℂ)^(k : ℤ)) = _
      rw [tsum_mul_right,tsum_mul_right,← Complex.conj_tsum,hsum,map_mul]
      simp only [map_ofNat]
      ring

theorem gamma0PeterssonInner_unfold (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (hk : 3 ≤ k) (hEven : Even k) (n : ℕ+) (F : UpperHalfPlane → ℂ)
    (hF : ∀ γ : CongruenceSubgroup.Gamma0 N, spectralHolomorphicSlash k (atkinRealMap γ.val) F = F)
    (hI : Integrable (spectralPeterssonStripIntegrand k n
      (spectralHolomorphicSlash k (gamma0TrueCuspScaling N a) F))) :
    gamma0PeterssonInner N k (gamma0PeterssonPoincare N a k (n : ℕ)) F =
      ∫ z, spectralPeterssonStripIntegrand k n (spectralHolomorphicSlash k (gamma0TrueCuspScaling N a) F) z := by
  let G := spectralPeterssonStripIntegrand k n (spectralHolomorphicSlash k (gamma0TrueCuspScaling N a) F)
  let σ := (gamma0TrueCuspScaling N a)⁻¹
  let U := gamma0PeterssonUnfoldedIntegrand N a k n F
  have hpres : MeasurePreserving (fun z : UpperHalfPlane => σ • z) volume volume := by
    change MeasurePreserving (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ σ • z) _ _
    exact measurePreserving_smul _ _
  have hemb : MeasurableEmbedding (fun z : UpperHalfPlane => σ • z) := by
    change MeasurableEmbedding (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ σ • z)
    exact measurableEmbedding_const_smul _
  have hU : Integrable U := hpres.integrable_comp_of_integrable hI
  have hi : (∫ z, U z) = ∫ z, G z := hpres.integral_comp hemb G
  have h := gamma0PeterssonRegion_integral_unfold N U hU
  have hpoint :
      (∫ z in gamma0InteriorRegion N, ∑' γ : CongruenceSubgroup.Gamma0 N, U (γ.val⁻¹ • z)) =
      (2 : ℂ)*gamma0PeterssonInner N k (gamma0PeterssonPoincare N a k (n : ℕ)) F := by
    calc
      _ = ∫ z in gamma0InteriorRegion N, (2 : ℂ)*
          UpperHalfPlane.petersson (k : ℤ) (gamma0PeterssonPoincare N a k (n : ℕ)) F z := by
        apply setIntegral_congr_fun (gamma0InteriorRegion_isOpen N).measurableSet
        intro z _
        exact gamma0PeterssonUnfoldedIntegrand_periodize N a k hk hEven n F hF z
      _ = _ := integral_const_mul (2 : ℂ) _
  rw [hpoint,hi] at h
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h

end ArtinMatthews
